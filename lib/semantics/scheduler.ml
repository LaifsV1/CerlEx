(** Layer 1 network scheduler for concurrent Core Erlang execution.

    Drives a [network_conf] -- a set of processes communicating over per-sender
    FIFO channels -- by alternating two phases:

    {b Phase 1 -- [maximise]}: advance all processes using [big_step_one],
    resolving [SR_Send] and [SR_Spawn] deterministically as they appear,
    until no process remains on either.  The result is a maximal
    configuration in the DPOR sense: [enabled(s) = {}], i.e. every live
    process is either [Done] or [SR_Receive] (Aronis et al., TACAS 2018).

    {b Phase 2 -- [schedule]}: branch on all receives of a maximal
    configuration.  For each [SR_Receive] process, candidates are one
    branch per incoming channel whose front message matches a clause, plus
    one timeout branch for any finite timeout.  The full set of successors
    is the Cartesian product of every process's individual choices: channels
    have a fixed destination so no two processes compete for the same
    channel, and all channel updates commute.

    {b [explore]} iterates the two phases, recurring on every successor
    branch until all branches are terminal or bounds are exhausted.

    {b Bounds} are global refs set once by the caller (e.g. via
    [Arg.Set_int]) and read-only during exploration.  Each function reads
    the relevant ref at entry and counts with a local variable, so
    concurrent branches do not share state:
    - [b0]: max total CEK reduction steps per round.  [maximise] reads
    [!b0] at entry.  Guards against a diverging process.
    - [b1]: max send/spawn resolutions per round.  [maximise] reads [!b1]
    at entry.  Guards against infinite spawning chains.  Always [b1 < b2]
    in useful configurations.
    - [b2]: total trace length measured in receive decisions (one per call
    to [schedule]).  [explore] stops when the trace in [scheduler_conf]
    contains [b2] receive events.  Sends and spawns do not count toward
    [b2]; they are bounded per-round by [b1].

    {b Traces.}  Every [scheduler_conf] carries an [epoch list] recording
    all network moves made to reach it.  Each [epoch] is either a
    [Commuting] batch (sends and spawns resolved during [maximise] --
    these events commute and their order is irrelevant to equivalence) or
    a [Scheduled] batch (receive and timeout decisions chosen during one
    [schedule] call -- these are the branching points).  The [b2] bound
    counts [Scheduled] epochs (i.e. branching depth); equivalence checking
    at Layer 2 compares the sequences of [Scheduled] epochs.

    {b Search order} ([search_order] ref) controls whether new and resumed
    processes are prepended (DFS, stack discipline) or appended (BFS,
    queue discipline) to [pending] in [maximise_state].

    @author Yu-Yang Lin
    @since 2026-05-26
 *)

open Sexplib.Std
open Ast
open Trace       (* trace_event, epoch, trace_length, pp_trace, trace_equiv *)
open Frontier    (* search_order (BFS|DFS), 'a frontier and its operations *)

(* -------------------------------------------------------------------- *)
(* Global configuration                                                  *)
(* -------------------------------------------------------------------- *)

(* [search_order] (BFS|DFS) lives in [Frontier], opened above. *)

let b0 : int ref = ref 50000   (** max CEK steps per round *)
let b1 : int ref = ref 200   (** max send/spawn resolutions per round *)
let b2 : int ref = ref 1000  (** max scheduled epochs (trace depth) *)
let memo_size : int ref = ref 0  (** memo set capacity; 0 = disabled *)
let sleep_set : bool ref = ref true  (** sleep-set scheduling: park spurious-wait confs (see notes/sleep_set_plan.md) *)
let gc : bool ref = ref true  (** GC parked confs no live conf can wake; on by default (see notes/parked_conf_gc_plan.md, Approach B) *)
let gc_refcount : bool ref = ref false  (** use the incremental refcount GC instead of the batch sweep (Approach B; same result) *)
let print_canon : bool ref = ref false  (** print canonical string of each state to stderr *)
let prefix_stats : bool ref = ref false  (** build the computation tree and report prefix-reuse statistics *)
let verbose : bool ref = ref true  (** branch is ~4x faster than a fn-ref: skips closure allocation when false *)
let next_conf_id : int ref = ref 0  (** monotone counter; reset at each [explore] entry *)

(** Tracks which bounds were breached; reset at each [explore] entry. *)
type bound_status = { b0_hit : bool; b1_hit : bool; b2_hit : bool }

let bound_status : bound_status ref = ref { b0_hit = false; b1_hit = false; b2_hit = false }

(** Reduction steps ([Reductions.big_step_one] calls) performed since the last
    reset.  This is the same unit [b0] budgets, so "effort" and "the step
    bound" cannot drift apart.  [explore] samples it around each [maximise]
    call and charges the difference to the node being expanded. *)
let reduction_steps : int ref = ref 0

let exn_count : int ref = ref 0

let set_b0 (bs : bound_status) = { bs with b0_hit = true }
let set_b1 (bs : bound_status) = { bs with b1_hit = true }
let set_b2 (bs : bound_status) = { bs with b2_hit = true }

(* -------------------------------------------------------------------- *)
(* Trace logging (trace types and [pp_trace] live in [Trace])            *)
(* -------------------------------------------------------------------- *)

let warn_b0 (t : epoch list) =
  bound_status := set_b0 !bound_status;
  if !verbose then
    Printf.eprintf "[bound] b0 (CEK step budget) exceeded:\n%s\n%!" (pp_trace t)

let warn_b1 (t : epoch list) =
  bound_status := set_b1 !bound_status;
  if !verbose then
    Printf.eprintf "[bound] b1 (send/spawn budget) exceeded:\n%s\n%!" (pp_trace t)

let warn_b2 (t : epoch list) =
  bound_status := set_b2 !bound_status;
  if !verbose then
    Printf.eprintf "[bound] b2 (trace length) exceeded:\n%s\n%!" (pp_trace t)

let log_done (t : epoch list) =
  if !verbose then
    Printf.eprintf "[trace] terminal (all done):\n%s\n%!" (pp_trace t)

let warn_deadlock (t : epoch list) =
  if !verbose then
    Printf.eprintf "[warning] deadlock (all processes waiting):\n%s\n%!" (pp_trace t)

let log_memo_prune (memo_count : int) (t : epoch list) =
  if !verbose then
    Printf.eprintf "[memo] pruned already-seen state (total pruned: %d):\n%s\n%!" memo_count (pp_trace t)

let warn_exception (pid : Ast.pid) (ex : Ast.raised_exception) (t : epoch list) =
  incr exn_count;
  if !verbose then
    Printf.eprintf "[warning] process %d uncaught exception: %s\n%s\n%!"
      pid
      (Format.asprintf "%a" Value_printer.pp_exception ex)
      (pp_trace t)


(* -------------------------------------------------------------------- *)
(* Scheduler configuration                                               *)
(* -------------------------------------------------------------------- *)

(** [network_conf] plus the trace of moves made to reach it.
    [trace] is in reverse chronological order (most recent epoch at head);
    events within each epoch likewise most-recent-first. *)
(** Per-path sleep-set wake state (see [notes/sleep_set_plan.md] §10).  Lives on
    each conf and threads strictly downward.  The flag state {b must} be
    per-path: a global accumulator would combine evidence from different paths
    (path A clears sleeper p1, path B clears p2) and wake a conf that no single
    execution wakes -- unsound.
    - [by_pid]: sleeper pid -> [(parked id, blocked_srcs, park_comp)].  Each
      entry is one flag (one still-blocked sleeping process of a parked conf),
      keyed by its pid so a waker on that pid is a single lookup, valued by the
      senders it passed over and its own clock entry at park time.  A waker
      from a source {e not} in that set {e and} whose send_clock[pid] <= park_comp
      is independent evidence and clears the flag (see [notes/sleep_set_plan.md]).
    - [count]: parked id -> number of its flags still uncleared along this path;
      reaches 0 exactly when the last flag clears, at which point the conf is
      woken.  Per-path too -- a shared counter would re-introduce the cross-path
      combination this design removes. *)
type wake_history = {
    by_pid : (int * pid list * int) list PidMap.t;
    count  : int PidMap.t;
  }

let empty_wake_history = { by_pid = PidMap.empty; count = PidMap.empty }

type scheduler_conf = {
    network        : network_conf;
    trace          : epoch list;
    id             : int;       (** unique ID assigned at creation by [make_successor] *)
    spec_chain_ids : int list;  (** IDs of this config + consecutive speculative ancestors,
                                    most-recent first; [[]] if this config is real *)
    history        : wake_history;
      (** Per-path sleep-set flags (see [wake_history]).  A successor inherits
          its parent's history; a schedule point augments it with the confs
          parked there; a waker clears flags in it.  All updates are local to
          this lineage -- a side branch can never write another's, so a parked
          conf is only ever woken by single-path evidence. *)
    wakers         : (pid * pid * clock) list;
      (** Transient: [(target pid, src, send_clock)] for each message that
          reached a pid in this conf's {e newest} round -- sends resolved during
          [maximise] (target = dst) and receives chosen during [schedule]
          (target = receiver).  Read once by [explore] to test wake evidence
          against [history], then irrelevant.  Not part of the canonical state.
          The {e send} entries are the load-bearing ones: the waker of a parked
          conf is usually a message {e sent} to the sleeper from a sibling
          lineage where the sleeper had already moved on. *)
    fresh_sleepers : pid list;
      (** Transient: pids of deferred processes whose wait this round was a
          {e fresh spurious choice} (a [Receive] sibling was offered the same
          round).  Only a conf all of whose deferred processes are fresh
          sleepers is eligible to be parked. *)
  }

(* -------------------------------------------------------------------- *)
(* Maximise state (one per round)                                        *)
(* -------------------------------------------------------------------- *)

(** Internal state of one [maximise] round. *)
type maximise_state = {
    pending  : process_conf list;           (** processes still to advance *)
    settled  : process_conf list;           (** Done or SR_Receive *)
    channels : channel PidMap.t PidMap.t;   (** current in-transit messages *)
    next_pid : pid;                         (** next pid for spawn allocation *)
    refs     : ref_env;                     (** symbolic ref state *)
    ets      : ets_state;                   (** ETS shared state *)
    fo       : fo_graph;                    (** forced-order event graph *)
    events   : trace_event list;            (** send/spawn events this round *)
    wake_targets : (pid * pid * clock) list; (** (dst, src, send_clock) of sends this round, for sleep-set wakeups *)
    b0       : int;                         (** remaining CEK step budget *)
    b1       : int;                         (** remaining send/spawn budget *)
  }

(* -------------------------------------------------------------------- *)
(* ETS state helpers (notes/ets_plan.md, deferred-op scheme)             *)
(* -------------------------------------------------------------------- *)

(** Strict happens-before on clocks. *)
let clock_lt (a : clock) (b : clock) : bool =
  clock_leq a b && not (clock_leq b a)

let clock_sum (c : clock) : int =
  PidMap.fold (fun _ n acc -> n + acc) c 0

let clock_set (p : pid) (n : int) (c : clock) : clock =
  if n <= 0 then PidMap.remove p c else PidMap.add p n c

let ets_unsupported what =
  failwith (Printf.sprintf "[ets] unsupported in v0: %s (see notes/ets_plan.md)" what)

(** Resolve a table argument (tid or named-table atom) to its table record.
    A dead named table remains resolvable: the name is unbound at death, but a
    read concurrent with the death may still order itself before it, so the
    record must be reachable to build that branch.  Multiple dead generations
    of the same name cannot be disambiguated without generation clocks --
    kill the exploration as unsupported rather than guess. *)
let ets_resolve (ets : ets_state) (tab : value) : ets_table option =
  match tab with
  | V_ets_tid tid -> List.find_opt (fun t -> t.tid = tid) ets.tables
  | V_atom n ->
    begin match List.assoc_opt n ets.names with
    | Some tid -> List.find_opt (fun t -> t.tid = tid) ets.tables
    | None ->
      begin match List.filter (fun t -> t.et_name = Some n) ets.tables with
      | []  -> None
      | [t] -> Some t
      | _   -> ets_unsupported "multiple dead generations of a named table"
      end
    end
  | _ -> None

let ets_replace_table (t' : ets_table) (ets : ets_state) : ets_state =
  { ets with tables = List.map (fun t -> if t.tid = t'.tid then t' else t) ets.tables }

(** ETS set-table key equality is exact ([=:=]). *)
let ets_key_eq = Term_order.erlang_exact_eq

(** Append a completed write event to the [(key, writer)] channel. *)
let ets_commit_write (t : ets_table) (key : value) (writer : pid)
    (obj : value) (wclock : clock) : ets_table =
  let w = { obj; wclock } in
  let rec add = function
    | [] -> [((key, writer), [w])]
    | ((k, p), ws) :: rest when p = writer && ets_key_eq k key ->
      ((k, p), ws @ [w]) :: rest
    | e :: rest -> e :: add rest
  in
  { t with writes = add t.writes }

(** The write channels for [key]: [(writer, events)] pairs, oldest-first. *)
let ets_channels (t : ets_table) (key : value) : (pid * ets_write list) list =
  List.filter_map (fun ((k, p), ws) ->
    if ets_key_eq k key then Some (p, ws) else None) t.writes

let ets_all_key_writes (t : ets_table) (key : value)
    : (pid * int * ets_write) list =
  ets_channels t key
  |> List.concat_map (fun (writer, ws) ->
      List.mapi (fun idx w -> (writer, idx, w)) ws)

let ets_find_table_by_tid (ets : ets_state) (tid : int) : ets_table =
  match List.find_opt (fun t -> t.tid = tid) ets.tables with
  | Some t -> t
  | None -> failwith "[ets] internal: table id not found"

let ets_update_table_by_tid (tid : int) (f : ets_table -> ets_table)
    (ets : ets_state) : ets_state =
  { ets with tables = List.map (fun t -> if t.tid = tid then f t else t) ets.tables }

(** Tombstone every live table owned by [p] (owner exit is an implicit,
    racing table delete -- see ets_plan.md).  [dc] is the exit event's clock
    (the dying process's clock, bumped once for the termination event).
    Returns the updated state and the tids killed, for trace events. *)
let ets_owner_exit (p : pid) (dc : clock) (ets : ets_state)
    : ets_state * int list =
  let killed = List.filter (fun t -> t.et_owner = p && t.dead = None) ets.tables in
  if killed = [] then (ets, [])
  else
    let killed_tids = List.map (fun t -> t.tid) killed in
    let tables = List.map (fun t ->
      if List.mem t.tid killed_tids then { t with dead = Some dc } else t) ets.tables in
    let names = List.filter (fun (_, tid) -> not (List.mem tid killed_tids)) ets.names in
    ({ tables; names }, killed_tids)

(** The key of an object under v0's [keypos = 1] restriction. *)
let ets_obj_key (obj : value) : value =
  match obj with
  | V_tuple (k :: _) -> k
  | _ -> failwith "[ets] internal: non-tuple object past Ets_bifs validation"

(** How a maximise-phase ETS resolution continues. *)
type ets_max_result =
  | Ets_resolved of ref_env * process_conf * ets_state * fo_graph * trace_event list
      (** forced/producer outcome: process continues, state updated.  The
          [ref_env] differs from the input only for [Ets_new], which
          allocates the tid as a reference (fresh id + creation stamp); the
          [fo_graph] differs only for the owner write, which commits a
          forced-order write node (plan §4.2). *)
  | Ets_settled
      (** observer: leave the process stuck for [schedule] *)

(** Resolve the forced and producer ETS cases (see the v0 scope table in
    ets_plan.md).  [alone] = no other process exists in this round (the
    init-case gate for named creation).  The process resumes on [cont],
    dropping the [E_Ets] frame. *)
let resolve_ets_maximise (conf : process_conf) (op : ets_op) (cont : eval_cxt)
    (refs : ref_env) (ets : ets_state) (fo : fo_graph) ~(alone : bool)
    : ets_max_result =
  let badarg ets evs =
    Ets_resolved (refs,
                  { conf with cek = { ecxt = cont
                                    ; term = T_Raise { class_ = Error
                                                     ; reason = V_atom "badarg"
                                                     ; info = V_nil } }
                            ; deferred = None }, ets, fo, evs) in
  (* A forced failure that OBSERVES table death commits like any observer:
     join the tombstone clock, then bump own component -- uniform with the
     schedule-phase badarg branches and the forced-dead lookup.  [badarg]
     above is for failures that observe no clocked event (unresolvable
     table/name, permission, bound-name init claim).  In the forced cases
     the join is a no-op (dc <= clock by forcedness); the bump is the
     observation event, and it matters for a process that catches the
     badarg and continues: dropping it loses the causal edge to the death
     the process just observed (an over-approximation for later reads). *)
  let badarg_death dc ets evs =
    Ets_resolved (refs,
                  { conf with cek = { ecxt = cont
                                    ; term = T_Raise { class_ = Error
                                                     ; reason = V_atom "badarg"
                                                     ; info = V_nil } }
                            ; deferred = None
                            ; clock = clock_bump conf.pid (clock_join conf.clock dc) },
                  ets, fo, evs) in
  (* Tids allocate from the shared ref id space with a creation stamp,
     exactly like [make_ref], so tid/tid ordering goes through the ordinary
     symbolic machinery (causally-ordered creations compare forced,
     concurrent ones branch).  The kind lives in the [V_ets_tid] constructor:
     mixed-kind ordering vs an ordinary ref is implementation-defined on
     BEAM and kills the exploration (see [Erlang_bifs.dispatch_r]). *)
  let alloc_tid (conf : process_conf) : int * clock * process_conf * ref_env =
    let tid = refs.next_id in
    let clock' = clock_bump conf.pid conf.clock in
    let refs' = { refs with next_id = tid + 1
                          ; stamps = (tid, (conf.pid, clock')) :: refs.stamps } in
    (tid, clock', { conf with clock = clock' }, refs')
  in
  match op with
  | Ets_new { tname = _; named = false } ->
    (* Unnamed creation: pure producer.  The tid value is fresh in this
       lineage; nothing observes the creation. *)
    let (tid, _, conf, refs') = alloc_tid conf in
    let t =
      { tid; et_owner = conf.pid; et_name = None; dead = None
      ; writes = [] } in
    let ets' = { ets with tables = t :: ets.tables } in
    Ets_resolved (refs',
                  { conf with cek = { ecxt = cont; term = T_Vals [V_ets_tid tid] }
                            ; deferred = None },
                  ets', fo,
                  [Ev_ets { pid = conf.pid; op = "new"; tid; arg = None }])
  | Ets_new { tname; named = true } ->
    (* Named creation is a claim race between live processes (confirmed
       against Concuerror, ets_plan.md).  v0 supports only the init case:
       the claiming process is alone, so the claim is forced. *)
    if not alone then
      ets_unsupported "named ets:new with other processes live (claim race)"
    else if List.mem_assoc tname ets.names then
      badarg ets []
    else begin
      let (tid, _, conf, refs') = alloc_tid conf in
      let t =
        { tid; et_owner = conf.pid; et_name = Some tname; dead = None
        ; writes = [] } in
      let ets' = { tables = t :: ets.tables
                 ; names = (tname, tid) :: ets.names } in
      Ets_resolved (refs',
                    { conf with cek = { ecxt = cont; term = T_Vals [V_atom tname] }
                              ; deferred = None },
                    ets', fo,
                    [Ev_ets { pid = conf.pid; op = "new"; tid; arg = Some (V_atom tname) }])
    end
  | Ets_insert { tab; obj } ->
    begin match ets_resolve ets tab with
    | None -> badarg ets []   (* no such table / name not (never) bound *)
    | Some t ->
      begin match t.dead with
      | Some dc ->
        if t.et_owner = conf.pid
           || clock_leq dc conf.clock
           || conf.deferred = Some Deferred_ets_write then
          (* Forced badarg: owner death is program-ordered with owner writes;
             a tombstone at-or-before the writer's clock cannot be reordered
             after it; a deferred write declined success-now, so a tombstone
             appearing later leaves badarg as the only outcome.  Death is
             observed: join + bump. *)
          badarg_death dc ets
            [Ev_ets { pid = conf.pid; op = "badarg"; tid = t.tid; arg = Some obj }]
        else
          Ets_settled   (* tombstone concurrent: both orders branch in schedule *)
      | None ->
        if t.et_owner = conf.pid then begin
          (* Owner-write fast path: only the owner (or its exit) can kill the
             table, and both are program-ordered after this write. *)
          let clock' = clock_bump conf.pid conf.clock in
          let key = ets_obj_key obj in
          let t' = ets_commit_write t key conf.pid obj clock' in
          let fo' = Forced_order.record_write fo conf.pid clock' t.tid key in
          Ets_resolved
            (refs,
             { conf with cek = { ecxt = cont; term = T_Vals [V_atom "true"] }
                       ; deferred = None; clock = clock' },
             ets_replace_table t' ets, fo',
             [Ev_ets { pid = conf.pid; op = "insert"; tid = t.tid; arg = Some obj }])
        end
        else Ets_settled  (* non-owner write: observer of table liveness *)
      end
    end
  | Ets_lookup { tab; _ } ->
    begin match ets_resolve ets tab with
    | None -> badarg ets []
    | Some _ -> Ets_settled   (* all lookup outcomes branch in schedule *)
    end
  | Ets_delete { tab } ->
    begin match ets_resolve ets tab with
    | None -> badarg ets []
    | Some t ->
      if t.et_owner <> conf.pid then
        (* Non-owner delete is a local badarg with no table effect (verified,
           owner-only rule).  A permission failure observes no clocked event:
           it fails the same way whether the table is live or dead. *)
        badarg ets []
      else begin match t.dead with
      | Some dc ->
        (* Owner delete on a dead table: the failure observes the death
           (join is a no-op -- an owner's tables die only by its own
           program-ordered delete). *)
        badarg_death dc ets []
      | None ->
        let clock' = clock_bump conf.pid conf.clock in
        let ets' = ets_replace_table { t with dead = Some clock' } ets in
        let ets' = { ets' with names = List.filter (fun (_, tid) -> tid <> t.tid) ets'.names } in
        Ets_resolved
          (refs,
           { conf with cek = { ecxt = cont; term = T_Vals [V_atom "true"] }
                     ; deferred = None; clock = clock' },
           ets', fo,
           [Ev_ets { pid = conf.pid; op = "delete"; tid = t.tid; arg = None }])
      end
    end

(* -------------------------------------------------------------------- *)
(* Forced-order matcher test (notes/forced_order_graph_plan.md §4.5)     *)
(* -------------------------------------------------------------------- *)

let fo_debug = Sys.getenv_opt "CERLEX_DEBUG_FO" <> None

(** [fo_matches mt refs dst clauses rho v]: would the retained receive
    matcher [(clauses, rho)] of process [dst] select message [v]?  Pure
    re-run of clause selection against the path's committed [refs]; ref
    constraints accumulated by guard evaluation are discarded.  Guards
    cannot read mutable process state (the guard fragment has no pdict
    access; [self()] needs only the pid), so a synthetic conf is faithful.
    [`Unknown] when a guard raises or the outcome differs across ref-order
    worlds: the fm edge is skipped -- the forced order is under-approximated
    in the sound direction (a cycle may be missed and the trace count stays
    an over-approximation, but nothing realisable is ever pruned). *)
let fo_matches (mt : Call_dispatch.module_table) (refs : ref_env) (dst : pid)
    (clauses : Syntax.Core_ast.clause list) (rho : env) (v : value)
    : [ `Match | `NoMatch | `Unknown ] =
  let synth = { pid      = dst
              ; cek      = { ecxt = []; term = T_Vals [] }
              ; env      = rho
              ; deferred = None
              ; pdict    = []
              ; clock    = PidMap.empty } in
  let outcomes = Reductions.select_clause mt refs synth [v] rho clauses in
  if List.for_all (fun (_, r) -> match r with Ok (Some _) -> true | _ -> false)
       outcomes
  then `Match
  else if List.for_all (fun (_, r) -> match r with Ok None -> true | _ -> false)
            outcomes
  then `NoMatch
  else begin
    if fo_debug then
      Printf.eprintf
        "[fo] matcher skip: guard exception or ref-world divergence (dst %d)\n%!"
        dst;
    `Unknown
  end

(** Retroactive first-match sources (plan §4.4): the consumed-send nodes of
    every committed receive at [dst] whose retained matcher takes the new
    message -- each contributes the arrival fact
    [Arr(consumed) < Arr(new send)].  Receive commits at [dst] are exactly
    [dst]'s own [Fo_recv] events ([fo_dst] = the committer's pid), so only
    that process's tick map is walked. *)
let fo_retro_fm_sources (mt : Call_dispatch.module_table) (refs : ref_env)
    (fo : fo_graph) (dst : pid) (msg : value) : fo_node list =
  match PidMap.find_opt dst fo.fo_events with
  | None -> []
  | Some ts ->
     TickMap.fold (fun _ (ev, _) acc ->
       match ev with
       | Fo_recv { fo_dst = _; fo_consumed; fo_clauses; fo_env } ->
          begin match fo_matches mt refs dst fo_clauses fo_env msg with
          | `Match -> fo_consumed :: acc
          | `NoMatch | `Unknown -> acc
          end
       | _ -> acc) ts []

(* -------------------------------------------------------------------- *)
(* Scheduler: Maximise                                                   *)
(* -------------------------------------------------------------------- *)

(** Append a process to [rs.pending]: back for BFS, front for DFS. *)
let enqueue (p : process_conf) (rs : maximise_state) : maximise_state =
  match !search_order with
  | BFS -> { rs with pending = rs.pending @ [p] }
  | DFS -> { rs with pending = p :: rs.pending }

(** Apply [f] to [channels.(dst).(src)], removing entries when empty. *)
let channel_update (dst : pid) (src : pid) (f : channel -> channel) (channels : channel PidMap.t PidMap.t)
    : channel PidMap.t PidMap.t =
  let inner = match PidMap.find_opt dst channels with
    | Some m -> m
    | None   -> PidMap.empty
  in
  let chan = match PidMap.find_opt src inner with
    | Some c -> c
    | None   -> { msgs = [] }
  in
  let chan' = f chan in
  let inner' = match chan'.msgs with
    | [] -> PidMap.remove src inner
    | _  -> PidMap.add src chan' inner
  in
  if PidMap.is_empty inner'
  then PidMap.remove dst channels
  else PidMap.add dst inner' channels

(** Append [msg] sent by [src] to the FIFO channel at [channels.(dst).(src)].
    The message carries a snapshot of the sender's commit clock; no bump. *)
let channel_send (src : pid) (src_clock : clock) (dst : pid) (msg : value)
    (channels : channel PidMap.t PidMap.t)
    : channel PidMap.t PidMap.t =
  channel_update dst src
    (fun c -> { msgs = c.msgs @ [{ value = msg
                                 ; send_clock = src_clock
                                 ; same_sender_visible = None }] })
    channels

(** Build the initial [process_conf] for a freshly spawned process.
    The child inherits a copy of the parent's commit clock; no bump on
    either side (inheritance acts like a message from parent at birth). *)
let spawn_process (new_pid : pid) (parent_clock : clock) (clo : closure) (args : value list)
    : process_conf =
  let vars' =
    List.fold_left2
      (fun acc x v -> VarMap.add x v acc)
      clo.clo_env.vars clo.clo_vars args
  in
  { pid          = new_pid
  ; cek          = { ecxt = []; term = T_Expr clo.clo_body }
  ; env          = { clo.clo_env with vars = vars' }
  ; deferred     = None
  ; pdict        = []
  ; clock        = parent_clock
  }

(** Drive [sc.network] to a maximal configuration, resolving SR_Send/SR_Spawn
    deterministically.  Reads [!b0] and [!b1] at entry. *)
let maximise (mt : Call_dispatch.module_table) (sc : scheduler_conf)
    : scheduler_conf list =
  let rec evaluate_pending (ms : maximise_state) : maximise_state list =
    match ms.pending with
    | [] -> [ms]
    | conf :: rest ->
       let ms = { ms with pending = rest } in
       if ms.b0 <= 0 then (warn_b0 sc.trace; [{ ms with pending = [] }])
       else
         let ms = { ms with b0 = ms.b0 - 1 } in
         incr reduction_steps;
         begin
           match Reductions.big_step_one mt ms.refs conf with
           | Running [ (refs', conf') ] ->
              (* Common sequential case (one successor): recurse directly so the
                 call stays in tail position and is eliminated (constant stack),
                 instead of routing through the non-tail [List.concat_map], which
                 parks a frame per step and overflows on long loops.  [@tailcall]
                 makes the requirement explicit -- the build fails if a future
                 edit moves this out of tail position. *)
              (evaluate_pending [@tailcall]) (enqueue conf' { ms with refs = refs' })
           | Running rcs ->
              (* Genuine multi-way branch (e.g. symbolic ref comparison): fan out.
                 Branch points are shallow along any path, so the non-tail
                 [concat_map] here does not grow the stack unboundedly. *)
              List.concat_map (fun (refs', conf') ->
                evaluate_pending (enqueue conf' { ms with refs = refs' })) rcs
           | Done (refs', conf') ->
              (match conf'.cek.term with
               | T_Raise ex -> warn_exception conf'.pid ex sc.trace
               | _ -> ());
              (* Owner exit (any reason, crash included) is an implicit racing
                 table delete: tombstone every live table the dying process
                 owns, stamped with its clock bumped once for the exit event. *)
              let ms =
                let dc = clock_bump conf'.pid conf'.clock in
                let (ets', killed) = ets_owner_exit conf'.pid dc ms.ets in
                if killed = [] then ms
                else { ms with
                       ets    = ets'
                     ; events = List.fold_left (fun evs tid ->
                                  Ev_ets { pid = conf'.pid; op = "owner_exit"
                                         ; tid; arg = None } :: evs)
                                  ms.events killed }
              in
              evaluate_pending { ms with refs = refs' }
           | Stuck (SR_Receive _, (refs', conf')) ->
              evaluate_pending { ms with refs = refs'; settled = conf' :: ms.settled }
           | Stuck (SR_Send { dst; msg }, (refs', conf')) ->
              if ms.b1 <= 0 then (warn_b1 sc.trace; evaluate_pending ms)
              else
                (* Send bump: the send is an event on the sender's own clock
                   component.  The bumped value is stamped on the message and
                   retained by the sender (full vector-clock send semantics).
                   Only the sender (conf'.pid) writes its own component, so
                   single-writer freshness -- on which the mailbox-order
                   flag-pruning relies -- is preserved. *)
                let conf' = { conf' with clock = clock_bump conf'.pid conf'.clock } in
                (* Send commit (plan §4.4): record the send node and the
                   retroactive first-match edges against already-committed
                   receives at [dst] (the message arrives after whatever
                   those receives consumed). *)
                let fo' = Forced_order.record_send ms.fo conf'.pid conf'.clock dst
                            (fo_retro_fm_sources mt refs' ms.fo dst msg) in
                let ms = { ms with
                           refs     = refs'
                         ; b1       = ms.b1 - 1
                         ; channels = channel_send conf'.pid conf'.clock dst msg ms.channels
                         ; fo       = fo'
                         ; events   = Ev_send { src = conf'.pid; dst; msg } :: ms.events
                         ; wake_targets = (dst, conf'.pid, conf'.clock) :: ms.wake_targets
                         } in
                evaluate_pending (enqueue conf' ms)
           | Stuck (SR_Spawn { clo; args; cont }, (refs', conf')) ->
              if ms.b1 <= 0 then (warn_b1 sc.trace; evaluate_pending ms)
              else
                let new_pid = ms.next_pid in
                let child   = spawn_process new_pid conf'.clock clo args in
                let spawner = { conf' with cek = { ecxt = cont; term = T_Vals [V_pid new_pid] } } in
                let ms = { ms with
                           refs     = refs'
                         ; b1       = ms.b1 - 1
                         ; next_pid = new_pid + 1
                         ; events   = Ev_spawn { parent = conf'.pid; child = new_pid } :: ms.events
                         }
                in
                evaluate_pending (enqueue spawner (enqueue child ms))
           | Stuck (SR_Ets { op; cont }, (refs', conf')) ->
              if ms.b1 <= 0 then (warn_b1 sc.trace; evaluate_pending ms)
              else
                let alone = ms.pending = [] && ms.settled = [] in
                begin match resolve_ets_maximise conf' op cont refs' ms.ets ms.fo ~alone with
                | Ets_resolved (refs'', conf'', ets', fo', evs) ->
                   (* Forced/producer resolution counts against b1 like a
                      send/spawn (guards infinite insert loops). *)
                   let ms = { ms with
                              refs   = refs''
                            ; b1     = ms.b1 - 1
                            ; ets    = ets'
                            ; fo     = fo'
                            ; events = evs @ ms.events } in
                   evaluate_pending (enqueue conf'' ms)
                | Ets_settled ->
                   evaluate_pending { ms with refs = refs'; settled = conf' :: ms.settled }
                end
         end
  in
  List.map (fun ms ->
    let trace' = match ms.events with
      | [] -> sc.trace
      | evs -> Commuting evs :: sc.trace
    in
    { network        = { processes = ms.settled
                       ; channels  = ms.channels
                       ; next_pid  = ms.next_pid
                       ; refs      = ms.refs
                       ; ets       = ms.ets
                       ; fo        = ms.fo
                       }
    ; trace          = trace'
    ; id             = sc.id
    ; spec_chain_ids = sc.spec_chain_ids
    ; history        = sc.history
    ; wakers         = ms.wake_targets   (* sends resolved this round wake parked sleepers *)
    ; fresh_sleepers = []                (* maximise produces no waits *)
    })
  (evaluate_pending
     { pending  = sc.network.processes
     ; settled  = []
     ; channels = sc.network.channels
     ; next_pid = sc.network.next_pid
     ; refs     = sc.network.refs
     ; ets      = sc.network.ets
     ; fo       = sc.network.fo
     ; events   = []
     ; wake_targets = []
     ; b0       = !b0
     ; b1       = !b1
     })

(* -------------------------------------------------------------------- *)
(* Scheduler: Schedule Deliveries                                        *)
(* -------------------------------------------------------------------- *)

(** One branch for one [SR_Receive] process per [schedule] round.
    [Receive]: the receive fires on [msg]; [new_chan] is the channel after removal.
    [Timeout]: timeout body runs.
    [Guard_exn]: guard raised; process unblocks with exception, channel unchanged, no event.
    [Waiting]: infinity timeout, no match -- process stays at [SR_Receive]. *)
type branch =
  | Receive   of { refs : ref_env; proc : process_conf; src : pid; msg : value; new_chan : channel
                 ; send_clock : clock                       (* snapshot from the consumed message *)
                 ; from_same_sender_visible : clock option  (* flag stamp, if the message was flagged *)
                 ; clauses : Syntax.Core_ast.clause list    (* the matcher this receive selected with... *)
                 ; rho : env                                (* ...and its env, retained for the
                                                              forced-order fm rules (plan §4.3) *)
                 ; consumed_send_node : fo_node
                 ; fm_targets : fo_node list
                   (* send nodes of the OTHER in-flight messages toward this
                      process that the matcher takes: the present-state fm
                      edge targets (plan §4.3), precomputed once per branch
                      in [scan_channel] rather than once per branch vector
                      in [record_vector] -- the branch recurs in every
                      sibling vector (6^6 of them at alltoall7's big point)
                      and the computation reads only the branch and the
                      shared pre-consumption state.  Evaluated under the
                      pre-branch [refs]: verdicts uniform across those ref
                      worlds persist under any refinement the vector's other
                      branches add, so this can differ from the per-vector
                      evaluation only by skipping an [`Unknown]-refined
                      match -- the sound under-approximation direction of
                      plan §4.5. *)
                 ; fm_endpoint_indexes : (int * int list) option
                   (* Source and target indexes into the schedule point's
                      parent reachability.  Filled once after every branch
                      set is known; reused by all sibling branch vectors. *)
                 }
  | Timeout   of process_conf
  | Guard_exn of { refs : ref_env; proc : process_conf }
  | Waiting   of { proc : process_conf; fresh : bool }
                 (** [fresh]: this round also offered the process a [Receive]
                     branch, so the wait is a {e genuine spurious choice} (it
                     declined an available message) -- the precondition for
                     parking it into the sleep set.  A wait with [fresh = false]
                     is a forced block (nothing matchable {e this} round) and
                     must keep progressing through the frontier.  ETS defer
                     branches reuse [Waiting] with [fresh = false]: explored
                     eagerly, never parked into the (receive) sleep set. *)
  | Ets_branch of { outcome : ets_outcome
                  ; update : ets_state -> ets_state  (* commit effect; [Fun.id] for pure observations *)
                  ; ev : trace_event
                  ; write : (pid * clock * int * value) option
                    (* [Some (writer, wclock, tid, key)] when the branch
                       lands a write: its forced-order node (plan §4.2) *) }
                 (** One scheduled ETS outcome (lookup result, non-owner
                     insert success, death-badarg).  Non-read [update]s from
                     one branch vector commute: writes land in per-writer
                     channels and table deaths are fixed lifecycle events. *)

and ets_outcome =
  | Ets_proc of process_conf
      (** ready successor (insert success, badarg): clock already final *)
  | Ets_read of ets_read_commit
      (** read: the resumed process (and its clock) is decided only in
          [finalize_ets_reads], after all same-round choices are known *)

and ets_read_obs =
  | Read_value of { tid : int
                  ; key : value
                  ; writer : pid
                  ; index : int
                  ; wclock : clock
                  ; obj : value }
  | Read_nil of { tid : int; key : value }

and ets_read_commit =
  { reader_pid : pid
  ; before_clock : clock
  ; obs : ets_read_obs
  ; finish : clock -> process_conf
  }

let deferred_receive_srcs = function
  | Some (Deferred_receive { srcs; _ }) -> srcs
  | _ -> []

let deferred_receive_timeout = function
  | Some (Deferred_receive { timeout; _ }) -> timeout
  | _ -> false

let has_deferred (p : process_conf) = Option.is_some p.deferred

let clear_deferred (p : process_conf) = { p with deferred = None }

let make_deferred_receive srcs timeout =
  let srcs = List.sort_uniq compare srcs in
  if srcs = [] && not timeout then None
  else Some (Deferred_receive { srcs; timeout })

(** Union ref creation stamps.  Stamp ids are globally unique (allocated from
    [next_id]), so a shared id always carries an identical stamp; concatenating
    while dropping ids already present yields the union. *)
let merge_stamps (s1 : (int * (pid * clock)) list) (s2 : (int * (pid * clock)) list) =
  List.fold_left (fun acc (id, v) -> if List.mem_assoc id acc then acc else (id, v) :: acc) s1 s2

(** Merge ref constraints from all branches in [bvec] into [base].
    Each [Receive]/[Guard_exn] branch carries a [refs'] that is [base] plus
    new ordering constraints added during guard evaluation.  For a valid
    branch vector those new constraints must be mutually consistent; if any
    pair is contradictory (cycle in the DAG) the combination is pruned.
    Stamps and [next_id] are merged once per branch (a branch may create a ref
    without adding any order edge). *)
let merge_branch_refs (base : ref_env) (bvec : branch list) : ref_env option =
  List.fold_left (fun acc_opt br ->
    match acc_opt with
    | None -> None
    | Some acc ->
      let br_refs = match br with
        | Receive { refs; _ } | Guard_exn { refs; _ } -> Some refs
        | _ -> None
      in
      match br_refs with
      | None -> Some acc
      | Some r ->
        let acc = { acc with next_id = max acc.next_id r.next_id
                           ; stamps  = merge_stamps acc.stamps r.stamps } in
        (* add_constraint skips edges already implied, so no pre-filtering needed *)
        List.fold_left (fun racc (a, b) ->
          match racc with
          | None -> None
          | Some refs ->
            match Ref_order.add_constraint refs.order a b with
            | None     -> None
            | Some ord -> Some { refs with order = ord }
        ) (Some acc) r.order
  ) (Some base) bvec

let ets_read_sort_key (r : ets_read_commit) =
  match r.obs with
  | Read_nil { tid; key = _ } ->
    (0, 0, [], tid, 0, 0, r.reader_pid)
  | Read_value { tid; writer; index; wclock; _ } ->
    (1, clock_sum wclock, PidMap.bindings wclock, tid, writer, index, r.reader_pid)

(** What a read's commit clock absorbs: the read-from edge, i.e. the clock of
    the write actually observed (an empty result observes nothing).  The
    anti-dependency "this read is after every read of an older value" is NOT
    folded in here -- it is carried by the forced-order graph's RW edges (see
    [Forced_order.saturate]); the observation stamps that used to add it were
    retired 2026-07-25, `notes/forced_order_handover.md` R1. *)
let ets_read_deps (obs : ets_read_obs) : clock =
  match obs with
  | Read_nil _ -> PidMap.empty
  | Read_value { wclock; _ } -> wclock

let ets_read_valid (ets : ets_state) (r : ets_read_commit) (clock' : clock) : bool =
  match r.obs with
  | Read_nil { tid; key } ->
    let t = ets_find_table_by_tid ets tid in
    begin match t.dead with
    | Some dc when clock_leq dc clock' -> false
    | _ ->
      not (List.exists (fun (_, _, w) -> clock_leq w.wclock clock')
             (ets_all_key_writes t key))
    end
  | Read_value { tid; key; writer; index; wclock; obj = _ } ->
    let t = ets_find_table_by_tid ets tid in
    begin match t.dead with
    | Some dc when clock_leq dc clock' -> false
    | _ ->
      let same_key = ets_all_key_writes t key in
      List.exists (fun (p, i, w) ->
        p = writer && i = index && w.wclock = wclock
      ) same_key
      && not (List.exists (fun (_, _, w') ->
        clock_leq w'.wclock clock' && clock_lt wclock w'.wclock
      ) same_key)
    end

let finalize_ets_reads (ets : ets_state) (fo : fo_graph) (reads : ets_read_commit list)
    : (ets_state * fo_graph * (pid * process_conf) list) option =
  let reads = List.sort (fun a b -> compare (ets_read_sort_key a) (ets_read_sort_key b)) reads in
  let rec loop ets fo finals = function
    | [] ->
      (* Joint-consistency check (plan §4.1): record the round's read nodes,
         then saturate the RW/WW rules over the whole event store.  A cycle
         means no linearisation realises this read vector; the vector is
         dropped like a ref-inconsistent one. *)
      begin match Forced_order.saturate fo with
      | Forced_order.Saturated fo' -> Some (ets, fo', finals)
      | Forced_order.Cycle _ -> None
      end
    | r :: rest ->
      let deps = ets_read_deps r.obs in
      let raw = clock_join r.before_clock deps in
      let tick = clock_get r.reader_pid r.before_clock + 1 in
      if clock_get r.reader_pid raw > tick then
        (* Unreachable by single-writer freshness: nothing the reader has
           not yet committed can appear in [deps].  Fail loudly rather than
           silently dropping a successor (plan §4 work-site note). *)
        failwith "[ets] internal: read deps exceed the reader's own next tick"
      else
        let clock' = clock_set r.reader_pid tick raw in
        if not (ets_read_valid ets r clock') then
          None
        else
          let (tid, key, from) = match r.obs with
            | Read_nil { tid; key } -> (tid, key, None)
            | Read_value { tid; key; writer; wclock; _ } ->
              (tid, key, Some (writer, clock_get writer wclock))
          in
          let fo' = Forced_order.record_event fo (r.reader_pid, tick)
              (Fo_read { fo_tid = tid; fo_key = key; fo_from = from }) clock' in
          loop ets fo' ((r.reader_pid, r.finish clock') :: finals) rest
  in
  loop ets fo [] reads

(** The send nodes that can be endpoints of schedule-local fm edges.  A
    Receive branch with no [fm_targets] records no such edge, so neither its
    consumed send node nor an empty target set needs a parent-reachability
    row. *)
let fm_endpoint_send_nodes (all_branches : branch list list) : FoNodeSet.t =
  List.fold_left (fun send_nodes branches ->
    List.fold_left (fun send_nodes branch ->
      match branch with
      | Receive { consumed_send_node; fm_targets; _ } when fm_targets <> [] ->
         List.fold_left (fun nodes target -> FoNodeSet.add target nodes)
           (FoNodeSet.add consumed_send_node send_nodes) fm_targets
      | Receive _ | Timeout _ | Guard_exn _ | Waiting _ | Ets_branch _ ->
         send_nodes
    ) send_nodes branches
  ) FoNodeSet.empty all_branches

let index_fm_endpoints (parent : Forced_order.parent_reachability)
    (branch : branch) : branch =
  match branch with
  (* [-no-fo]: the parent relation is empty and the indexes are never used
     ([record_vector]'s fm call returns at once), so skip the lookups, which
     would otherwise fail on the absent endpoints. *)
  | Receive r when r.fm_targets <> [] && !Forced_order.enabled ->
     let source_index =
       Forced_order.endpoint_index parent r.consumed_send_node in
     let target_indexes =
       List.map (Forced_order.endpoint_index parent) r.fm_targets in
     Receive { r with
       fm_endpoint_indexes = Some (source_index, target_indexes) }
  | Receive _ | Timeout _ | Guard_exn _ | Waiting _ | Ets_branch _ ->
     branch

(** Record the forced-order events and edges for one branch vector (plan §4.2
    non-owner writes, §4.3 receives), against the pre-consumption network
    state.  A write landing cannot close a cycle ([record_write] fails
    loudly if one does).  When a receive fires, it records its node and the
    present-state fm edges: every
    other in-flight message toward the destination that the retained matcher
    takes must arrive after the consumed one (consuming it proved no
    matching message sat earlier in mailbox order).  [None] when an fm
    edge closes a cycle: the branch vector is jointly unrealisable.

    [parent_reachability] contains only the immutable parent graph.
    [branch_vector_reachability] starts from that relation and absorbs the
    earlier fm edges from this branch vector.  It is reset before the next
    sibling; the full graph accumulated by this fold is likewise private to
    this branch vector. *)
let record_vector (parent_reachability : Forced_order.parent_reachability)
    (branch_vector_reachability : Forced_order.branch_vector_reachability)
    (sc : scheduler_conf) (branch_vector : branch list)
    : fo_graph option =
  Forced_order.reset_branch_vector_reachability
    parent_reachability branch_vector_reachability;
  List.fold_left (fun acc branch ->
    match acc with
    | None -> None
    | Some fo ->
      match branch with
      | Ets_branch { write = Some (wpid, wclock, tid, key); _ } ->
         Some (Forced_order.record_write fo wpid wclock tid key)
      | Ets_branch { write = None; _ } | Timeout _ | Guard_exn _ | Waiting _ ->
         Some fo
      | Receive
          { proc; clauses; rho; consumed_send_node = consumed
          ; fm_targets; fm_endpoint_indexes; _ } ->
         let d = proc.pid in
         let fo = Forced_order.record_event fo (d, clock_get d proc.clock)
             (Fo_recv { fo_dst = d; fo_consumed = consumed
                      ; fo_clauses = clauses; fo_env = rho })
             proc.clock in
         (* fm targets were computed once per branch in [scan_channel]
            (see the [fm_targets] field); only recording and the cycle
            check are per branch vector -- a cycle can span several fm
            edges from this vector (recv_fifo_cycle), so they cannot move. *)
         begin match fm_targets, fm_endpoint_indexes with
         | _, None when not !Forced_order.enabled -> Some fo  (* -no-fo *)
         | [], None -> Some fo
         | _, Some (source_index, target_indexes) ->
            Forced_order.record_arrival_edges_with_parent_reachability
              parent_reachability branch_vector_reachability
              fo consumed source_index fm_targets target_indexes
         | _ :: _, None ->
            failwith "[forced_order] internal: fm endpoint indexes missing"
         end
  ) (Some sc.network.fo) branch_vector

(** Build one successor from [branch_vector] (one [branch] per process).
    Returns [None] if all branches are [Waiting], if the ref ordering
    constraints from individual branches are mutually inconsistent, or if
    the vector's forced-order relation is cyclic (jointly unrealisable).
    Note: [processes] order is reversed by the fold; sort at [explore] level if needed. *)
let make_successor (parent_reachability : Forced_order.parent_reachability)
    (branch_vector_reachability : Forced_order.branch_vector_reachability)
    (sc : scheduler_conf) (branch_vector : branch list)
    : scheduler_conf option =
  if List.for_all (function Waiting _ -> true | _ -> false) branch_vector
  then None
  else
    match merge_branch_refs sc.network.refs branch_vector with
    | None -> None
    | Some refs ->
      match
        record_vector parent_reachability branch_vector_reachability
          sc branch_vector
      with
      | None -> None
      | Some fo ->
      let (channels, ets, evs, recvs, fresh, reads) =
        List.fold_left
          (fun (chs, ets, evs, recvs, fresh, reads) branch ->
            match branch with
            | Receive { proc; src; msg; new_chan; send_clock; _ } ->
               (channel_update proc.pid src (fun _ -> new_chan) chs,
                ets,
                Ev_receive { receiver = proc.pid; src; msg } :: evs,
                (proc.pid, src, send_clock) :: recvs,
                fresh,
                reads)
            | Timeout proc ->
               (chs, ets, Ev_timeout { receiver = proc.pid } :: evs, recvs, fresh, reads)
            | Guard_exn _ ->
               (chs, ets, evs, recvs, fresh, reads)
            | Ets_branch { update; ev; outcome; _ } ->
               (chs, update ets, ev :: evs, recvs, fresh,
                match outcome with Ets_proc _ -> reads | Ets_read r -> r :: reads)
            | Waiting { proc; fresh = f } ->
               let fresh' = if f then proc.pid :: fresh else fresh in
               (chs, ets, evs, recvs, fresh', reads))
          (sc.network.channels, sc.network.ets, [], [], [], [])
          branch_vector
      in
      match finalize_ets_reads ets fo reads with
      | None -> None
      | Some (ets, fo, read_procs) ->
        let read_proc pid =
          match List.assoc_opt pid read_procs with
          | Some p -> p
          | None -> failwith "[ets] internal: finalized read process not found"
        in
        let processes =
          List.fold_left (fun procs branch ->
            match branch with
            | Receive { proc; _ }
            | Timeout proc
            | Guard_exn { proc; _ }
            | Waiting { proc; _ } ->
              proc :: procs
            | Ets_branch { outcome = Ets_proc proc; _ } ->
              proc :: procs
            | Ets_branch { outcome = Ets_read r; _ } ->
              read_proc r.reader_pid :: procs
          ) [] branch_vector
        in
        let new_id = let i = !next_conf_id in incr next_conf_id; i in
        let is_speculative = List.exists (function Waiting _ -> true | _ -> false) branch_vector in
        Some { network        = { processes
                                ; channels
                                ; next_pid = sc.network.next_pid
                                ; refs
                                ; ets
                                ; fo
                                }
             ; trace          = (match evs with [] -> sc.trace | _ -> Scheduled evs :: sc.trace)
             ; id             = new_id
             ; spec_chain_ids = if is_speculative then new_id :: sc.spec_chain_ids else []
             ; history        = sc.history
             ; wakers          = recvs
             ; fresh_sleepers = fresh
             }

(** Compute the branch set for one [SR_Receive] process.
    Scans each incoming channel for the first matching message. *)
let schedule_deliveries (mt : Call_dispatch.module_table) (refs : ref_env) (conf : process_conf)
    (channels : channel PidMap.t PidMap.t) : branch list =
  let (clauses, timeout, timeout_body, rho, cont) = match conf.cek with
    | { term = T_Vals [timeout]; ecxt = E_Receive (clauses, timeout_body, rho) :: cont } ->
      (clauses, timeout, timeout_body, rho, cont)
    | _ -> failwith "[schedule_deliveries] process not at E_Receive"
  in
  (* fm candidates (plan §4.3, hoisted): the send nodes of every in-flight
     message toward this process that the matcher takes -- ALL channels,
     deferred senders included (fm is a fact about arrival order, not about
     what this round may consume).  Shared by all this process's [Receive]
     branches (each filters out its own consumed message), and lazy so a
     round that produces no [Receive] branch pays nothing. *)
  let fm_candidates = lazy (
    match PidMap.find_opt conf.pid channels with
    | None -> []
    | Some inbox ->
      PidMap.fold (fun src' ch acc ->
        List.fold_left (fun acc m ->
          match fo_matches mt refs conf.pid clauses rho m.value with
          | `Match -> (src', clock_get src' m.send_clock) :: acc
          | `NoMatch | `Unknown -> acc
        ) acc ch.msgs
      ) inbox [])
  in
  (* [prefix]: non-matching messages in reverse; implicit arg: channel message list.
     [List.rev_append prefix rest] reconstructs the channel without the matched message.
     Returns a list of branches: one per (refs', result) outcome from [select_clause].
     An [Ok None] outcome continues scanning the remaining messages with the updated [refs'].
     Prefix messages are written back flagged ([same_sender_visible = Some flag_clock]):
     a message passed over to reach a later match from the same sender is guaranteed
     to be in the receiver's mailbox (FIFO).  The flag stamp is the receiver's
     post-commit clock; first flag wins (an already-flagged message keeps its stamp). *)
  let rec scan_channel refs src prefix = function
    | [] -> []
    | msg :: rest ->
      List.concat_map (fun (refs', result) ->
        match result with
        | Ok None ->
          scan_channel refs' src (msg :: prefix) rest
        | Ok (Some (rho', body)) ->
          (* Receive commit: join the consumed message's send clock, bump own
             component -- the only increment in the clock protocol. *)
          let new_clock = clock_bump conf.pid (clock_join conf.clock msg.send_clock) in
          let proc    = { conf with cek = { ecxt = cont; term = T_Expr body }
                                  ; env = rho'
                                  ; clock = new_clock } in
          let stamp p = match p.same_sender_visible with
            | Some _ -> p
            | None   -> { p with same_sender_visible = Some new_clock }
          in
          let new_chan = { msgs = List.rev_append (List.map stamp prefix) rest } in
          let consumed = (src, clock_get src msg.send_clock) in
          [Receive { refs = refs'; proc; src; msg = msg.value; new_chan
                   ; send_clock = msg.send_clock
                   ; from_same_sender_visible = msg.same_sender_visible
                   ; clauses; rho
                   ; consumed_send_node = consumed
                   ; fm_targets =
                       List.filter (fun n -> n <> consumed)
                         (Lazy.force fm_candidates)
                   ; fm_endpoint_indexes = None }]
        | Error ex ->
          let proc = { conf with cek = { ecxt = cont; term = T_Raise ex } } in
          [Guard_exn { refs = refs'; proc }]
      ) (Reductions.select_clause mt refs conf [msg.value] rho clauses)
  in
  (* [inbox]: map from sender pid to channel, i.e. all channels arriving at [conf.pid].
     Channels from deferred senders are skipped -- the process already passed over their
     front message in a previous round and cannot reach it again without first consuming it.
     Each channel scan yields zero or more branches (one per ref-ordering world). *)
  let old_srcs = deferred_receive_srcs conf.deferred in
  let branches =
    match PidMap.find_opt conf.pid channels with
    | None -> []
    | Some inbox ->
      PidMap.fold (fun src chan acc ->
        if List.mem src old_srcs then acc
        else (scan_channel refs src [] chan.msgs) @ acc
      ) inbox []
  in
  (* Collect the src pids that produced a Receive branch this round;
     these become newly deferred in the Waiting branch. *)
  let new_deferred_srcs = List.filter_map (function
    | Receive { src; _ } -> Some src
    | _ -> None) branches
  in
  (* Advancing branches (Receive, Guard_exn) clear deferral; the process is leaving
     the receive. *)
  let branches = List.map (function
    | Receive r   -> Receive   { r with proc = clear_deferred r.proc }
    | Guard_exn r -> Guard_exn { r with proc = clear_deferred r.proc }
    | b           -> b) branches
  in
  (* Mailbox-order pruning (commit clocks; notes/vector_clocks_plan.md §3):
     drop a Receive branch on message M when a sibling Receive branch exists on
     a flagged message S whose flag commit happens-before send(M), i.e.
     M.send_clock[r] >= S.flag_clock[r] with r = conf.pid.  S was in r's
     mailbox at flag time; M entered behind it; both match the current clauses;
     a receive takes the first match in mailbox order -- M can never win.
     Sound because only r bumps r's component: a sender can only know a value
     >= the flag stamp via a causal chain from the flag commit.
     Guard: a flagged branch prunes only if its match added no ref ordering
     constraints (brefs.order = refs.order); otherwise S matches only in some
     ref worlds and pruning M would lose the worlds where it does not (§6). *)
  let flag_thresholds =
    List.mapi (fun i b -> (i, b)) branches
    |> List.filter_map (function
      | (i, Receive { from_same_sender_visible = Some fc; refs = brefs; _ })
        when brefs.order = refs.order ->
        Some (i, clock_get conf.pid fc)
      | _ -> None)
  in
  let branches =
    match flag_thresholds with
    | [] -> branches
    | _ ->
      List.filteri (fun i b ->
        match b with
        | Receive { send_clock; _ } ->
          let sent = clock_get conf.pid send_clock in
          not (List.exists (fun (j, t) -> j <> i && sent >= t) flag_thresholds)
        | _ -> true
      ) branches
  in
  (* If this receive can consume an already-visible same-sender message, it cannot
     sleep or timeout.  Keep sibling Receive branches, though: without a global
     mailbox order, an unmarked cross-sender branch may represent a message that
     arrived before the same-sender-visible one. *)
  let has_same_sender_visible_match =
    List.exists (function
      | Receive { from_same_sender_visible = Some _; _ } -> true
      | _ -> false
    ) branches
  in
  if has_same_sender_visible_match then
    branches
  else
  (* Always append a Waiting branch when no same-sender-visible message matches.
     The waiting proc records the alternatives covered by siblings: receive
     branches for sender srcs and, when finite, the timeout branch. *)
  let old_timeout = deferred_receive_timeout conf.deferred in
  let deferred_srcs = old_srcs @
    List.filter (fun s -> not (List.mem s old_srcs)) new_deferred_srcs
  in
  let timeout_offered = match timeout with
    | V_atom "infinity" -> false
    | _ -> not old_timeout
  in
  let waiting_deferred = make_deferred_receive deferred_srcs (old_timeout || timeout_offered) in
  let branches = branches @
    [Waiting { proc = { conf with deferred = waiting_deferred }
             ; fresh = new_deferred_srcs <> [] }] in
  if not timeout_offered then branches
  else
    let proc = { conf with cek = { ecxt = cont; term = T_Expr timeout_body }
                         ; env  = rho
                         ; deferred = None } in
    Timeout proc :: branches

(* -------------------------------------------------------------------- *)
(* Scheduler: Schedule ETS observers (notes/ets_plan.md)                 *)
(* -------------------------------------------------------------------- *)

let ets_badarg_term =
  T_Raise { class_ = Error; reason = V_atom "badarg"; info = V_nil }

(** Compute the branch set for one process stuck on an ETS observer op.
    The forced and producer cases were already resolved by [maximise] (which
    runs first every round), so this sees only: non-owner inserts on live or
    concurrently-dead tables, deferred inserts still waiting, and lookups.
    [others_live] gates the defer branch: with no other process, no future
    write or death can appear, so deferring is pointless (and would strand
    the product). *)
let schedule_ets (ets : ets_state) ~(others_live : bool) (conf : process_conf)
    : branch list =
  let (op, cont) = match conf.cek with
    | { term = T_Vals []; ecxt = E_Ets op :: cont } -> (op, cont)
    | _ -> failwith "[schedule_ets] process not at E_Ets"
  in
  let badarg_proc clock' =
    { conf with cek = { ecxt = cont; term = ets_badarg_term }
              ; deferred = None; clock = clock' } in
  match op with
  | Ets_insert { tab; obj } ->
    let t = match ets_resolve ets tab with
      | Some t -> t
      | None -> failwith "[schedule_ets] settled insert on unresolvable table"
    in
    begin match conf.deferred with
    | Some Deferred_ets_write ->
      begin match t.dead with
      | None ->
        (* Declined success-now; still waiting for a tombstone (maximise
           resolves the forced badarg as soon as one appears). *)
        [Waiting { proc = conf; fresh = false }]
      | Some dc ->
        (* The tombstone can land in the SAME maximise round, after this
           process was already settled (a producer later in the round's
           pending order lays it), so "maximise would have forced this" is
           not an invariant.  Resolve here exactly as maximise would next
           round: the one remaining outcome is the forced badarg observing
           the death (success-now was declined; the sibling covers it).
           A Waiting branch instead would be wrong: if every other process
           is also Waiting, the all-Waiting vector is pruned and the badarg
           world would be lost. *)
        [ Ets_branch
            { outcome = Ets_proc (badarg_proc (clock_bump conf.pid (clock_join conf.clock dc)))
            ; update = Fun.id
            ; ev = Ev_ets { pid = conf.pid; op = "badarg"; tid = t.tid; arg = Some obj }
            ; write = None } ]
      end
    | _ ->
      let key = ets_obj_key obj in
      let clock' = clock_bump conf.pid conf.clock in
      let success =
        Ets_branch
          { outcome = Ets_proc { conf with cek = { ecxt = cont; term = T_Vals [V_atom "true"] }
                                         ; deferred = None; clock = clock' }
          ; update = (fun ets ->
              match ets_resolve ets tab with
              | Some t -> ets_replace_table (ets_commit_write t key conf.pid obj clock') ets
              | None   -> ets (* unreachable: table records persist *))
          ; ev = Ev_ets { pid = conf.pid; op = "insert"; tid = t.tid; arg = Some obj }
          ; write = Some (conf.pid, clock', t.tid, key) }
      in
      begin match t.dead with
      | None ->
        (* Live table, non-owner writer: success now, or wait for the only
           future event that changes the outcome -- table death. *)
        [ success
        ; Waiting { proc = { conf with deferred = Some Deferred_ets_write }
                  ; fresh = false } ]
      | Some dc ->
        (* Tombstone concurrent with the writer (the forced case resolved in
           maximise): both orders are reachable and both materialise now. *)
        let badarg =
          Ets_branch
            { outcome = Ets_proc (badarg_proc (clock_bump conf.pid (clock_join conf.clock dc)))
            ; update = Fun.id
            ; ev = Ev_ets { pid = conf.pid; op = "badarg"; tid = t.tid; arg = Some obj }
            ; write = None }
        in
        [badarg; success]
      end
    end

  | Ets_lookup { tab; key; elem } ->
    let t = match ets_resolve ets tab with
      | Some t -> t
      | None -> failwith "[schedule_ets] settled lookup on unresolvable table"
    in
    let cr = conf.clock in
    let (seen, nil_offered) = match conf.deferred with
      | Some (Deferred_ets_lookup { seen; nil_offered }) -> (seen, nil_offered)
      | _ -> ([], false)
    in
    begin match t.dead with
    | Some dc when clock_leq dc cr ->
      (* Reader causally after the table's death: forced badarg. *)
      [ Ets_branch
          { outcome = Ets_proc (badarg_proc (clock_bump conf.pid cr))
          ; update = Fun.id
          ; ev = Ev_ets { pid = conf.pid; op = "badarg"; tid = t.tid; arg = Some key }
          ; write = None } ]
    | _ ->
      let channels = ets_channels t key in
      (* Read coherence is purely clock-based -- no shared-state commitment.
         A write [w] is STALE for this reader iff some strictly-newer
         same-key write is already forced ([<= Cr]): the reader (or its
         causal past) has observed a write that overwrote [w], so no
         linearisation extending that observation can return [w].  Notably
         this keeps concurrent readers independent (reads do not conflict) --
         one reader observing the new value must not stop another from still
         reading the old one.  A stateful truncation of overwritten prefixes
         was tried first and got depend_1 wrong in both directions (spurious
         [] badmatches, then missing old-value reads); see ets_plan.md. *)
      let all_writes = List.concat_map snd channels in
      let stale w =
        List.exists (fun w' ->
          clock_leq w'.wclock cr && clock_lt w.wclock w'.wclock) all_writes
      in
      let has_forced =
        List.exists (fun w -> clock_leq w.wclock cr) all_writes
      in
      (* Value branches: per writer channel, every event past the deferred
         high-water mark ([seen]) that is not stale.
         NOTE: (YY/VK) we looked at it and it seems ok. it's not possible to have
         future values: values written after this read don't need to be filtered.
         adding a filter would be a NO-OP (or ID).
       *)
      let value_branches =
        List.concat_map (fun (p, ws) ->
          let seen_p = match List.assoc_opt p seen with Some n -> n | None -> 0 in
          List.mapi (fun idx w -> (idx, w)) ws
          |> List.filter (fun (idx, _) -> idx + 1 > seen_p)
          |> List.filter (fun (_, w) -> not (stale w))
          |> List.map (fun (idx, w) -> (p, idx, w))
        ) channels
        |> List.map (fun (p, idx, w) ->
          (* The resumed process and its commit clock are decided in
             [finalize_ets_reads] (deps join + bump + re-validation), via
             [finish]. *)
          Ets_branch
            { outcome = Ets_read
                { reader_pid = conf.pid
                ; before_clock = cr
                ; obs = Read_value
                    { tid = t.tid; key; writer = p; index = idx
                    ; wclock = w.wclock; obj = w.obj }
                ; finish = (fun clock' ->
                    match elem with
                    | None ->
                      { conf with cek = { ecxt = cont; term = T_Vals [V_cons (w.obj, V_nil)] }
                                ; deferred = None; clock = clock' }
                    | Some pos ->
                      begin match w.obj with
                      | V_tuple vs when pos <= List.length vs ->
                        { conf with cek = { ecxt = cont; term = T_Vals [List.nth vs (pos - 1)] }
                                  ; deferred = None; clock = clock' }
                      | _ -> badarg_proc clock'   (* position out of range *)
                      end) }
            ; update = Fun.id
            ; ev = Ev_ets { pid = conf.pid; op = "lookup"; tid = t.tid; arg = Some w.obj }
            ; write = None })
      in
      (* [] branch: only when no write is forced visible (rule 1, over the
         full history), at most once per lookup ([] later is identical to
         [] now).  For lookup_element a missing key is badarg. *)
      let nil_available = (not nil_offered) && not has_forced in
      let nil_branches =
        if not nil_available then []
        else
          [ Ets_branch
              { outcome = Ets_read
                  { reader_pid = conf.pid
                  ; before_clock = cr
                  ; obs = Read_nil { tid = t.tid; key }
                  ; finish = (fun clock' ->
                      match elem with
                      | None ->
                        { conf with cek = { ecxt = cont; term = T_Vals [V_nil] }
                                  ; deferred = None; clock = clock' }
                      | Some _ -> badarg_proc clock') }
              ; update = Fun.id
              ; ev = Ev_ets { pid = conf.pid; op = "lookup_nil"; tid = t.tid; arg = Some key }
              ; write = None } ]
      in
      (* Death branch: a concurrent tombstone can be ordered before the read. *)
      let death_branches = match t.dead with
        | Some dc ->
          [ Ets_branch
              { outcome = Ets_proc (badarg_proc (clock_bump conf.pid (clock_join cr dc)))
              ; update = Fun.id
              ; ev = Ev_ets { pid = conf.pid; op = "badarg"; tid = t.tid; arg = Some key }
              ; write = None } ]
        | None -> []
      in
      (* Defer branch: wait for a future write (or death).  Pointless once
         the table is dead (its state can never change again) or when no
         other process exists. *)
      let defer_branches =
        if t.dead <> None || not others_live then []
        else
          let seen' = List.map (fun (p, ws) -> (p, List.length ws)) channels in
          let marker = Deferred_ets_lookup
              { seen = seen'
              ; nil_offered = nil_offered || nil_branches <> [] } in
          [Waiting { proc = { conf with deferred = Some marker }; fresh = false }]
      in
      value_branches @ nil_branches @ death_branches @ defer_branches
    end

  | Ets_new _ | Ets_delete _ ->
    failwith "[schedule_ets] new/delete are always resolved in maximise"

(** [schedule mt sc]: branch on all stuck processes (Cartesian product of
    per-process branch sets): receives via [schedule_deliveries], ETS
    observers via [schedule_ets].  Pure branching; no bounds. *)
let schedule (mt : Call_dispatch.module_table) (sc : scheduler_conf)
    : scheduler_conf list =
  let others_live = match sc.network.processes with _ :: _ :: _ -> true | _ -> false in
  let all_branches = List.map (fun p ->
    match p.cek.ecxt with
    | E_Ets _ :: _ -> schedule_ets sc.network.ets ~others_live p
    | _ -> schedule_deliveries mt sc.network.refs p sc.network.channels
  ) sc.network.processes in
  let fm_send_nodes = fm_endpoint_send_nodes all_branches in
  let parent_reachability =
    Forced_order.parent_reachability sc.network.fo fm_send_nodes in
  let all_branches =
    List.map
      (List.map (index_fm_endpoints parent_reachability))
      all_branches
  in
  let branch_vector_reachability =
    Forced_order.branch_vector_reachability parent_reachability in
  List.filter_map
    (make_successor
       parent_reachability branch_vector_reachability sc)
    (Utils.cartesian_product_fast all_branches)

(** [terminal_speculative_after_local_settle mt sc] recognises speculative
    successors that would be pushed only to be popped, locally reduced, and
    immediately counted as speculative terminal branches.

    This is deliberately conservative: it only looks through local CEK work
    that reaches [Done] or [SR_Receive].  If any branch would send or spawn,
    the successor remains live because it may create messages that unblock the
    speculative wait. *)
let terminal_speculative_after_local_settle (mt : Call_dispatch.module_table) (sc : scheduler_conf)
    : int option =
  if not (List.exists has_deferred sc.network.processes) then
    None
  else
    let rec evaluate pending settled refs b0 =
      match pending with
      | [] ->
        Some [{ sc with network = { sc.network with processes = settled; refs } }]
      | conf :: rest ->
        if b0 <= 0 then
          None
        else begin
          (* The pruning probe is real work: charge it like maximise's steps,
             or the metric would credit us for effort we actually spent. *)
          incr reduction_steps;
          match Reductions.big_step_one mt refs conf with
          | Running rcs ->
            map_concat_option (fun (refs', conf') ->
              evaluate (conf' :: rest) settled refs' (b0 - 1)
            ) rcs
          | Done (refs', _) ->
            evaluate rest settled refs' (b0 - 1)
          | Stuck (SR_Receive _, (refs', conf')) ->
            evaluate rest (conf' :: settled) refs' (b0 - 1)
          | Stuck (SR_Send _, _) | Stuck (SR_Spawn _, _) ->
            None
          | Stuck (SR_Ets _, _) ->
            (* Conservative: an ETS op may branch or mutate shared state. *)
            None
        end
    and map_concat_option f = function
      | [] -> Some []
      | x :: xs ->
        match f x, map_concat_option f xs with
        | Some ys, Some zs -> Some (ys @ zs)
        | _ -> None
    in
    let only_waiting_branches sc =
      sc.network.processes <> []
      && List.exists has_deferred sc.network.processes
      && List.for_all (fun p ->
        match p.cek with
        | { term = T_Vals [_]; ecxt = E_Receive _ :: _ } ->
          schedule_deliveries mt sc.network.refs p sc.network.channels
          |> List.for_all (function Waiting _ -> true | _ -> false)
        | _ -> false
      ) sc.network.processes
    in
    match evaluate sc.network.processes [] sc.network.refs !b0 with
    | Some states when states <> [] && List.for_all only_waiting_branches states ->
      Some (List.length states)
    | _ -> None

(* -------------------------------------------------------------------- *)
(* Sleep set (notes/sleep_set_plan.md)                                   *)
(* -------------------------------------------------------------------- *)

(** [parkable_sleepers sc] is [Some sleepers] when [sc] is a {e genuine spurious
    wait} eligible for the sleep set: it has at least one deferred process and
    {e every} deferred process is a {e fresh} sleeper (its wait this round was
    offered alongside a [Receive] branch -- it declined an available message).

    Requiring freshness -- rather than "declined something at some point" -- is
    what keeps parking sound.  A fresh wait always has a sibling [Receive] branch
    kept in the frontier this round, so the lineage that carries the waker
    exists.  Two failure modes this rules out, both of which would strand a
    delivery path (an under-approximation -- the wrong direction):
    - {b Stale decline (proxy_2).}  A process force-blocked {e now} (e.g.
      waiting for a message still travelling down a forwarding chain) declined
      something earlier but has no [Receive] sibling this round; parking it would
      freeze the very chain that would deliver to it.  [fresh = false] there.
    - {b Empty channel (request/reply).}  A process blocked with nothing
      matchable has no [Receive] branch at all, so it is never fresh.

    Returns, for each sleeper, its pid, its blocked sources (the senders it
    passed over), and its own clock entry at park time -- the data that
    becomes its wake flag. *)
let parkable_sleepers (sc : scheduler_conf) : (pid * pid list * int) list option =
  let deferred = List.filter has_deferred sc.network.processes in
  if deferred <> [] && List.for_all (fun p -> List.mem p.pid sc.fresh_sleepers) deferred
  then Some (List.map (fun p -> (p.pid, deferred_receive_srcs p.deferred, clock_get p.pid p.clock)) deferred)
  else None

(* The per-flag wake test is inline in [try_wake]: a flag clears when (a) the
   waker's source is not in the sleeper's blocked_srcs (same-sender FIFO) AND
   (b) the waker's send_clock[sleeper_pid] <= park_comp (the clock gate: the
   sender did not observe the sleeper after the park point).  See
   [notes/sleep_set_plan.md]. *)

(* -------------------------------------------------------------------- *)
(* Explorer                                                              *)
(* -------------------------------------------------------------------- *)

(** Exhaustively explore from [sc], alternating [maximise] and [schedule].
    Logs a [warning] to stderr when a bound is exceeded.
    Prints a summary line ([done] traces: N real, ...) on completion. *)
let explore (mt : Call_dispatch.module_table) (sc : scheduler_conf) : unit =
  exn_count := 0;
  reduction_steps := 0;
  next_conf_id := sc.id + 1;
  let count             = ref 0 in
  let memo_count        = ref 0 in
  let speculative_count = ref 0 in   (* speculative endpoints: configs that end in (pruned) speculation, one per config *)
  let deadlock_count    = ref 0 in
  let max_frontier      = ref 0 in
  let total_pushed      = ref 0 in
  let spec_set : (int, unit) Hashtbl.t = Hashtbl.create 64 in
  let exploration_tree =
    if !prefix_stats then
      Some (Exploration_tree.create ~root_id:sc.id
              ~root_speculative:(List.exists has_deferred sc.network.processes))
    else
      None in
  let tree_add parent succ =
    Option.iter (fun tree ->
      Exploration_tree.add tree ~id:succ.id ~parent:parent.id
        ~speculative:(List.exists has_deferred succ.network.processes))
      exploration_tree in
  let tree_expanded conf =
    Option.iter (fun tree -> Exploration_tree.mark_expanded tree conf.id)
      exploration_tree in
  let tree_terminal ?(multiplicity = 1) conf kind =
    Option.iter (fun tree ->
      Exploration_tree.mark_terminal ~multiplicity tree conf.id kind)
      exploration_tree in
  let tree_terminal_id id kind =
    Option.iter (fun tree -> Exploration_tree.mark_terminal tree id kind)
      exploration_tree in
  let debug_sleep = Sys.getenv_opt "CERLEX_DEBUG_SLEEP" = Some "1" in
  let debug_gc    = Sys.getenv_opt "CERLEX_DEBUG_GC" = Some "1" in
  let no_sleep    = (not !sleep_set) || Sys.getenv_opt "CERLEX_NO_SLEEP" = Some "1" in
  (* Incremental refcount GC instead of the batch [gc_sweep] (same Approach B
     result).  Enabled by [-gc-refcount] or [CERLEX_GC_REFCOUNT=1]; needs [gc] on. *)
  let use_refcount = !gc && (!gc_refcount || Sys.getenv_opt "CERLEX_GC_REFCOUNT" = Some "1") in
  (* GC high-water mark: sweep when [parked_by_id] grows past it, then reset to
     twice the post-sweep size (floor [gc_floor]) so sweeps amortise (see
     [gc_sweep]).  [CERLEX_GC_HWM] overrides the floor, mainly to force sweeps on
     small inputs in tests (where counts must stay identical to a no-GC run). *)
  let gc_floor =
    match Option.bind (Sys.getenv_opt "CERLEX_GC_HWM") int_of_string_opt with
    | Some n when n >= 0 -> n
    | _ -> 10000 in
  let gc_hwm = ref gc_floor in
  (* Sleep set.  [parked_by_id] holds confs deferred out of the frontier; safe
     to key globally on the unique conf id (no cross-world pid ambiguity).
     [flags_by_id] holds each parked conf's sleeper pids still lacking wake
     evidence -- when it empties the conf is revived exactly once (the id is
     deleted, so a later wake attempt finds it already gone). *)
  (* Global, keyed on unique conf id: the parked confs themselves.  The flag
     state is NOT here -- it lives per-path in each conf's [history].  This map
     only stores id -> conf (to fetch on wake) and enforces wake-once. *)
  let parked_by_id : (int, scheduler_conf) Hashtbl.t =
    if no_sleep then Hashtbl.create 0 else Hashtbl.create 64 in
  (* Incremental refcount GC (notes/parked_conf_gc_plan.md), used when
     [use_refcount].  [refcount.(id)] = number of *live* confs (on the frontier or
     parked) whose [history.count] carries [id].  When it falls to 0 the parked
     conf [id] has no carrier left, can never wake, and is GC'd -- and GCing it
     [rc_leave]s it, cascading to the ids it carried.  Sound because the carrier
     graph is a DAG (a conf carries only ids parked at strict ancestors).  GC is
     *deferred* to [flush_gc] at a settled point (top of [run_round]): a conf that
     leaves the frontier is replaced by successors that re-carry its ids, so the
     count dips to 0 transiently; deferring past the matching [rc_enter]s avoids a
     false GC.  [rc_enter]/[rc_leave] are called at the pool-transition choke
     points: frontier add (enter), frontier pop (leave), park (enter), revive
     (leave), GC (leave). *)
  let refcount : (int, int) Hashtbl.t =
    if use_refcount then Hashtbl.create 256 else Hashtbl.create 0 in
  let gc_candidates : int Stack.t = Stack.create () in
  let rc_enter (c : scheduler_conf) : unit =
    if use_refcount then
      PidMap.iter (fun id _ ->
        let n = match Hashtbl.find_opt refcount id with Some n -> n | None -> 0 in
        Hashtbl.replace refcount id (n + 1))
        c.history.count in
  let rc_leave (c : scheduler_conf) : unit =
    if use_refcount then
      PidMap.iter (fun id _ ->
        match Hashtbl.find_opt refcount id with
        | Some n when n > 1 -> Hashtbl.replace refcount id (n - 1)
        | Some _ -> Hashtbl.remove refcount id; Stack.push id gc_candidates
        | None  -> ())   (* id already revived/GC'd: no longer tracked *)
        c.history.count in
  let park (succ : scheduler_conf) : unit =
    if debug_sleep then Printf.eprintf "[sleep] park id=%d\n%!" succ.id;
    Hashtbl.replace parked_by_id succ.id succ;
    (* [succ] is now a live (parked) carrier of the ids in its history -- count it;
       and queue [succ.id] so [flush_gc] GCs it if no kept sibling ends up carrying
       it (the 0-initial-carrier case, which [rc_leave] would never raise). *)
    if use_refcount then (rc_enter succ; Stack.push succ.id gc_candidates)
    (* The conf is OFF the frontier, so it is deliberately NOT added to
       [spec_set] here -- it counts as a speculative *configuration* only when
       woken back into the frontier (see [try_wake]).  Its flags are written
       into the kept siblings' histories at the schedule point (augmentation). *)
  in
  (* Process [sc]'s wakers (messages that reached a pid this round) against its
     own per-path [history]: clear the flags they are evidence for, and revive
     any parked conf whose last flag just fell.  Returns the conf with its flag
     state updated (so successors inherit the cleared flags) and the list of
     revived confs.  The hot check touches only the local history; the global
     [parked_by_id] is consulted only at an actual wake. *)
  let try_wake (sc : scheduler_conf) : scheduler_conf * scheduler_conf list =
    if PidMap.is_empty sc.history.by_pid then (sc, []) else
    let (hist, woken_ids) =
      List.fold_left (fun (hist, woken) (p, s, m) ->
        match PidMap.find_opt p hist.by_pid with
        | None -> (hist, woken)
        | Some flags ->
          (* A flag (id, blocked, park_comp) on pid p clears iff:
             (a) source [s] is not a sender the sleeper passed over (FIFO), and
             (b) send_clock[p] <= park_comp (sender did not observe the sleeper
                 after its park point -- the clock gate).

             The <= is load-bearing.  While a process is parked it is frozen,
             but a sibling branch may advance it through a timeout/receive and
             send causally-dependent messages that later target the parked pid.
             Those messages carry a larger p-component and must not revive the
             old parked receive.  See sleep_set_clock_gate_probe. *)
          let m_p = clock_get p m in
          let (cleared, remaining) =
            List.partition (fun (_id, blocked, park_comp) ->
              not (List.mem s blocked) && m_p <= park_comp) flags in
          if cleared = [] then (hist, woken)
          else
            let by_pid =
              if remaining = [] then PidMap.remove p hist.by_pid
              else PidMap.add p remaining hist.by_pid in
            let (count, woken) =
              List.fold_left (fun (count, woken) (id, _, _) ->
                let n = (match PidMap.find_opt id count with Some n -> n | None -> 1) - 1 in
                if n <= 0 then (PidMap.remove id count, id :: woken)
                else (PidMap.add id n count, woken)
              ) (hist.count, woken) cleared in
            ({ by_pid; count }, woken)
      ) (sc.history, []) sc.wakers
    in
    let revived =
      List.filter_map (fun id ->
        match Hashtbl.find_opt parked_by_id id with
        | Some pk ->
          if debug_sleep then Printf.eprintf "[sleep] wake id=%d\n%!" id;
          Hashtbl.remove parked_by_id id;   (* wake-once *)
          (* [pk] leaves the parked pool (it re-enters the frontier below, where
             it is [rc_enter]ed again).  Stop tracking [pk.id] -- it is no longer a
             GC candidate now that it is woken, not GC'd. *)
          if use_refcount then (Hashtbl.remove refcount id; rc_leave pk);
          (* Now entering the frontier as a (still-deferred) speculative conf. *)
          Hashtbl.replace spec_set pk.id ();
          Some pk
        | None -> None   (* already revived along another path *)
      ) woken_ids
    in
    ({ sc with history = hist }, revived)
  in
  (* Batch history-reachability GC of parked confs (notes/parked_conf_gc_plan.md,
     Approach B).  A parked conf is woken only via [try_wake], which fires only
     when a *live* conf's per-path [history.count] still carries its id -- either
     a frontier conf directly, or another still-parked conf that itself revives
     and then wakes it.  So the wakeable parked ids are exactly those reachable,
     in the [history.count] graph, from the ids carried by the current frontier.
     Any parked conf whose id is unreachable can never wake: drop it, counting it
     as the speculative endpoint it would have been tallied as at completion
     (frontier-empty case below) -- so the reported counts are unchanged.

     This batch sweep recomputes reachability from scratch; it is the obviously
     sound realisation of the refcount+cascade in the notes (the refcount is the
     planned incremental optimisation). *)
  let gc_sweep (frontier : scheduler_conf frontier) : unit =
    if Hashtbl.length parked_by_id = 0 then () else begin
      let live : (int, unit) Hashtbl.t =
        Hashtbl.create (Hashtbl.length parked_by_id) in
      let queue : int Queue.t = Queue.create () in
      let add_id id =
        if not (Hashtbl.mem live id) then (Hashtbl.add live id (); Queue.add id queue) in
      (* Roots: every parked id carried by a live frontier conf. *)
      let seed (c : scheduler_conf) = PidMap.iter (fun id _ -> add_id id) c.history.count in
      List.iter seed frontier.front;
      List.iter seed frontier.back;
      (* Propagate through still-parked carriers: a live parked conf keeps the
         confs *it* could wake (its own [history.count] keys) live too. *)
      while not (Queue.is_empty queue) do
        match Hashtbl.find_opt parked_by_id (Queue.take queue) with
        | None -> ()  (* carried id not currently parked (already woken/swept) *)
        | Some pk -> PidMap.iter (fun id _ -> add_id id) pk.history.count
      done;
      let dead =
        Hashtbl.fold (fun id _ acc -> if Hashtbl.mem live id then acc else id :: acc)
          parked_by_id [] in
      List.iter (fun id ->
        tree_terminal_id id Exploration_tree.Speculative;
        Hashtbl.remove parked_by_id id;
        incr speculative_count) dead;
      if debug_gc then
        Printf.eprintf "[gc] swept %d, parked %d->%d\n%!"
          (List.length dead) (List.length dead + Hashtbl.length parked_by_id)
          (Hashtbl.length parked_by_id)
    end
  in
  let maybe_gc (frontier : scheduler_conf frontier) : unit =
    if !gc && not use_refcount && Hashtbl.length parked_by_id > !gc_hwm then begin
      gc_sweep frontier;
      gc_hwm := max gc_floor (2 * Hashtbl.length parked_by_id)
    end
  in
  (* Drain GC candidates at a settled point: a queued [id] is GC'd iff it is still
     parked and its refcount is gone (0 carriers).  GCing it [rc_leave]s it, which
     may queue more candidates -- the [while] runs the cascade to a fixpoint. *)
  let flush_gc () =
    if use_refcount then
      while not (Stack.is_empty gc_candidates) do
        let id = Stack.pop gc_candidates in
        if not (Hashtbl.mem refcount id) then
          match Hashtbl.find_opt parked_by_id id with
          | Some pk ->
            tree_terminal_id id Exploration_tree.Speculative;
            Hashtbl.remove parked_by_id id;
            incr speculative_count;   (* the speculative endpoint it would have been at completion *)
            if debug_gc then Printf.eprintf "[gc/rc] id=%d, parked->%d\n%!" id (Hashtbl.length parked_by_id);
            rc_leave pk               (* cascade to the ids [pk] carried *)
          | None -> ()                (* not parked (revived or already GC'd) *)
      done
  in
  let check_memo =
    if !memo_size > 0 then
      let memo = Memoisation.make_bounded_set !memo_size "" in
      (fun sc -> Memoisation.add memo (Canonical.to_string sc.network))
    else
      (fun _ -> true)
  in
  let rec run_round frontier =
    flush_gc ();   (* settled point: GC parked confs whose carriers all left (refcount) *)
    if frontier_is_empty frontier then begin
      (* Parked confs never revived are spurious-wait endpoints: count each once
         as speculative (they were diverted from the frontier, never explored). *)
      Hashtbl.iter (fun id _ ->
        tree_terminal_id id Exploration_tree.Speculative) parked_by_id;
      speculative_count := !speculative_count + Hashtbl.length parked_by_id;
      let bs = !bound_status in
      let completeness =
        let exceeded = List.filter_map Fun.id
          [ (if bs.b0_hit then Some "b0" else None)
          ; (if bs.b1_hit then Some "b1" else None)
          ; (if bs.b2_hit then Some "b2" else None) ]
        in
        match exceeded with
        | [] -> "complete"
        | bs -> "incomplete: " ^ String.concat ", " bs ^ " exceeded"
      in
      (* -no-fo: say so in the output.  Counts are over-approximating without
         the graph, so a line that did not mention it would be misleading. *)
      let completeness =
        if !Forced_order.enabled then completeness
        else completeness ^ "; forced-order OFF: counts over-approximate" in
      Printf.printf "[done] traces: %d real, %d speculative, %d pruned by memo; failures: %d/%d deadlocked, %d uncaught exceptions; configurations: %d pushed, %d max frontier, %d speculative (%s)\n%!"
        !count !speculative_count !memo_count !deadlock_count !count !exn_count !total_pushed !max_frontier (Hashtbl.length spec_set) completeness
      ; Option.iter (fun tree ->
          let complete =
            !memo_count = 0
            && not bs.b0_hit && not bs.b1_hit && not bs.b2_hit in
          Printf.printf "%s\n%!"
            (Exploration_tree.summary_line ~complete tree))
        exploration_tree
    end else begin
      let (sc, frontier) = frontier_pop frontier in
      rc_leave sc;   (* [sc] leaves the frontier; its successors re-enter below *)
      if !print_canon then
        Printf.eprintf "[canon] %s\n%!" (Canonical.to_string sc.network);
      if check_memo sc then begin
        if trace_length sc.trace >= !b2 then
          (tree_terminal sc Exploration_tree.Cutoff;
           warn_b2 sc.trace;
           run_round frontier)
        else begin
          tree_expanded sc;
          let steps_before = !reduction_steps in
          let scs = maximise mt sc in
          (* Every successor below descends from this maximise, so its local
             reduction cost is the cost of expanding [sc].  Branching rounds
             share their prefix work; the counter records what was performed. *)
          Option.iter (fun tree ->
            Exploration_tree.add_steps tree sc.id (!reduction_steps - steps_before))
            exploration_tree;
          let successors = List.concat_map (fun sc' ->
            (* Sends resolved during this maximise may clear wake flags in this
               lineage's history (the common case: the waker was sent to the
               sleeper from a sibling world where the sleeper had already moved
               on).  [try_wake] returns [sc'] with those flags cleared, so the
               schedule successors below inherit the updated history. *)
            let (sc', woken_by_sends) = try_wake sc' in
            let scheduled = schedule mt sc' in
            List.iter (tree_add sc) scheduled;
            match scheduled with
            | [] ->
              if List.exists has_deferred sc'.network.processes then begin
                tree_terminal sc Exploration_tree.Speculative;
                incr speculative_count;
                if !verbose then
                  Printf.eprintf "[speculative] branch terminated with deferred processes:\n%s\n%!"
                    (pp_trace sc'.trace)
              end else begin
                tree_terminal sc Exploration_tree.Real;
                incr count;
                List.iter (Hashtbl.remove spec_set) sc.spec_chain_ids;
                if sc'.network.processes = [] then
                  log_done sc'.trace
                else begin
                  incr deadlock_count;
                  warn_deadlock sc'.trace
                end
              end;
              woken_by_sends
            | succs ->
              (* Confs parked at THIS schedule point: [(id, sleeper pids)].
                 Used below to augment every kept sibling's wake history. *)
              let parked_here = ref [] in
              let kept = List.filter_map (fun succ ->
                let probe_steps_before = !reduction_steps in
                let terminal = terminal_speculative_after_local_settle mt succ in
                (* The probe is real online work, but it is not part of a
                   root-to-real-leaf replay.  In particular, work proving a
                   speculative sibling terminal must not be multiplied by the
                   number of real descendants of its parent. *)
                Option.iter (fun tree ->
                  Exploration_tree.add_overhead_steps tree succ.id
                    (!reduction_steps - probe_steps_before))
                  exploration_tree;
                match terminal with
                | Some n ->
                  tree_terminal ~multiplicity:n succ Exploration_tree.Speculative;
                  (* Pruned speculative dead-end(s).  Do NOT count these as
                     traces: they were never pushed as configurations, so
                     counting them would make speculative traces exceed configs.
                     The per-branch verbose log below still records them. *)
                  if !verbose then
                    Printf.eprintf "[speculative] pruned %d terminal deferred branch%s before frontier push:\n%s\n%!"
                      n (if n = 1 then "" else "es") (pp_trace succ.trace);
                  None
                | None ->
                  match (if no_sleep then None else parkable_sleepers succ) with
                  | Some sleepers ->
                    (* Genuine spurious wait: defer out of the frontier into the
                       sleep set instead of exploring it now.  [sleepers] is
                       [(sleeper_pid, blocked_srcs, park_comp)] -- the flags this
                       conf contributes to its kept siblings' histories. *)
                    park succ;
                    parked_here := (succ.id, sleepers) :: !parked_here;
                    None
                  | None ->
                    if List.exists has_deferred succ.network.processes
                    then Hashtbl.replace spec_set succ.id ()
                    else List.iter (Hashtbl.remove spec_set) sc.spec_chain_ids;
                    Some succ
              ) succs in
              (* Augment each kept sibling's history with the confs parked here:
                 a kept conf may later deliver an independent message to one of
                 their sleepers and so must carry the right to wake them. *)
              let kept =
                match !parked_here with
                | [] -> kept
                | parked ->
                  (* Every kept sibling here was built from the same [sc'] and so
                     shares one [history]; add the confs parked here as flags
                     (one [(id, blocked_srcs)] per sleeper, keyed by sleeper pid;
                     [count id] = number of sleepers) ONCE and share the result
                     across all siblings. *)
                  let augmented =
                    List.fold_left (fun (h : wake_history) (id, sleepers) ->
                      let by_pid =
                        List.fold_left (fun by_pid (p, blocked, park_comp) ->
                          let old = Option.value (PidMap.find_opt p by_pid) ~default:[] in
                          PidMap.add p ((id, blocked, park_comp) :: old) by_pid
                        ) h.by_pid sleepers
                      in
                      { by_pid; count = PidMap.add id (List.length sleepers) h.count }
                    ) sc'.history parked
                  in
                  (* [rev_map] (tail-recursive) not [map]: [kept] can be the
                     whole Cartesian product of one schedule point (e.g. ~280k
                     successors for alltoall7) and stdlib [map] is not
                     tail-recursive.  Order is irrelevant -- these become an
                     unordered frontier. *)
                  List.rev_map (fun s -> { s with history = augmented }) kept
              in
              (* Each kept conf's own receives this round may clear flags in its
                 history; thread the cleared history onto it and collect revivals. *)
              let woken_by_recvs = ref [] in
              let kept =
                (* tail-recursive: see the [rev_map] note above -- [kept] can be
                   very large and order does not matter for the frontier. *)
                List.rev_map (fun k ->
                  let (k', w) = try_wake k in
                  if w <> [] then woken_by_recvs := w @ !woken_by_recvs;
                  k'
                ) kept
              in
              (* If nothing was kept and nothing was parked here, every successor
                 was a pruned terminal dead-end: this config is a speculative
                 endpoint, counted once.  (Parked confs are counted as speculative
                 at completion if never revived.) *)
              if kept = [] && !parked_here = [] then incr speculative_count;
              (* [rev_append] tail-recursive in [kept] (the potentially huge
                 successor list); the woken lists are small.  Order is
                 irrelevant for the frontier. *)
              List.rev_append kept (woken_by_sends @ !woken_by_recvs)
          ) scs in
          let n = List.length successors in
          total_pushed := !total_pushed + n;
          if use_refcount then List.iter rc_enter successors;   (* successors enter the frontier *)
          let frontier = frontier_add successors frontier in
          if frontier_size frontier > !max_frontier then
            max_frontier := frontier_size frontier;
          maybe_gc frontier;
          run_round frontier
        end
      end else begin
        tree_terminal sc Exploration_tree.Cutoff;
        incr memo_count;
        log_memo_prune !memo_count sc.trace;
        run_round frontier
      end
    end
  in
  run_round (frontier_add [sc] empty_frontier)
