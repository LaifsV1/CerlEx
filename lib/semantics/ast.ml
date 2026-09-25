(** Runtime AST for Core Erlang reductions.

    This module defines two layers of runtime structures:

    - {b Layer 0 (Process) -- CEK machine}: values, closures,
      environments, evaluation contexts, process configurations, and
      internal raised exceptions.  Used by [Reductions] and the BIF
      dispatch modules.

    - {b Layer 1 (Network) -- scheduler}: channels, stuck reasons, and the
      network configuration.  Used by the scheduler (not yet
      implemented).

    The source Core Erlang AST (as parsed) is defined separately in [Core_ast].

    @author Yu-Yang Lin
    @since 2026-04-12
 *)

open Sexplib.Std
open Syntax.Core_ast

(* Zarith arbitrary-precision integers with a hand-written sexp_of converter,
   since zarith 1.14 does not bundle sexplib support.  Only sexp_of is needed
   here because ast.ml derives [sexp_of] but not [of_sexp]. *)
type zint = Z.t
let sexp_of_zint n = Sexplib0.Sexp.Atom (Z.to_string n)

(* we only derive printing functions for Functors; i.e. only sexp_of_t, no t_of_sexp *)

module type OrderedSexpOf = sig
  type t
  val compare   : t -> t -> int
  val sexp_of_t : t -> Sexplib0.Sexp.t
end

module MakeSexpOfMap (Key : OrderedSexpOf) = struct
  include Map.Make (Key)
  let sexp_of_t : type a. (a -> Sexplib0.Sexp.t) -> a t -> Sexplib0.Sexp.t =
    fun sexp_of_a m ->
    [%sexp_of: (Key.t * a) list] (bindings m)
end

(* -------------------------------------------------------------------- *)
(* Layer 0 (Process) -- CEK machine                                      *)
(* -------------------------------------------------------------------- *)

type pid = int [@@deriving sexp]

module PidKey = struct
  type t = pid
  let compare = compare
  let sexp_of_t = sexp_of_pid
end

module VarKey = struct
  type t = var_name
  let compare = compare
  let sexp_of_t = sexp_of_var_name
end

module FnameKey = struct
  type t = fname
  let compare = compare
  let sexp_of_t = sexp_of_fname
end

module PidMap   = MakeSexpOfMap(PidKey)
module VarMap   = MakeSexpOfMap(VarKey)
module FnameMap = MakeSexpOfMap(FnameKey)

type closure = {
    clo_vars : var_name list;
    clo_body : expr;
    clo_env  : env;
  }
[@@deriving sexp_of]

(** value type needed because literals alone don't recursively include closures.
    Bitstrings are represented as [(bits, len_bits)]: [bits] is the integer
    value of the bitstring read MSB-first (big-endian natural order), and
    [len_bits] is the total number of bits.  Encoding/decoding is in
    [Bitstring_codec].
 *)
and value =
  | V_int of zint
  | V_float of float
  | V_char of char
  | V_atom of atom
  | V_ref of int             (* symbolic reference; int is the unique ID *)
  | V_ets_tid of int         (* ETS table id.  A reference on BEAM (OTP 22+),
                                but a DISTINCT KIND (magic ref): allocated from
                                the same [ref_env] id space with a creation
                                stamp, so same-kind ordering shares the
                                symbolic ref machinery -- but mixed-kind
                                ordering vs an ordinary ref is
                                implementation-defined on BEAM (measured
                                2026-07-07: NOT creation-ordered), so the kind
                                is carried in the constructor and mixed
                                ordering kills the exploration.  See
                                notes/ets_plan.md. *)
  | V_nil
  | V_cons of value * value  (* [x1, ..., xn | t] is represented as nested V_cons; includes improper lists *)
  | V_tuple of value list
  | V_binary of zint * int   (* (bits, len_bits): integer value MSB-first; len_bits = total bit count *)
  | V_closure of closure     (* closures are pattern matched by variables *)
  | V_pid of pid             (* runtime value, not part of source syntax *)
  | V_map of (value * value) list  (* sorted assoc-list; keys in Erlang term order *)
[@@deriving sexp_of]

(** this is the rho in the Core specs *)
and env = {
    vars : value VarMap.t;
    funs : closure FnameMap.t;
  }
[@@deriving sexp_of]

and value_seq = value list   (* results are actually sequences of values according to specs *)
[@@deriving sexp_of]

and exception_class =
  | Error
  | Exit
  | Throw
[@@deriving sexp_of]

and raised_exception = {
    class_ : exception_class;
    reason : value;
    info   : value;
  }
[@@deriving sexp_of]

(** We choose LEFT to RIGHT evaluation, whereas officially it's undefined (remember to flag impure subexp).
    Since we have a language with closures, we keep an environment (rho) around. This is so when we go up
    a frame after evaluating an inner expression, we continue evaluating the outexpression with the old rho.
    NOTE: we only support compiler-normalised Core; i.e. no strings or list literals.
 *)
and eval_frame =             
  | E_ValList of value list * expr list * env   (* resulting value sequences; different to lists *)
  | E_Tuple of value list * expr list * env
  | E_ConsHd of value list * expr list * expr * env
  | E_ConsTl of value list                      (* handles evaluation of tail *)
  | E_BitstrLhs of (zint * int) * expr list * bitstring list * env
  | E_BitstrRhs of (zint * int) * value * value list * expr list * bitstring list * env
  | E_Let of var_name list * expr * env
  | E_Case of clause list * env
  | E_ApplyFun of expr list * env
  | E_ApplyArgs of value * value list * expr list * env
  | E_QCallMod of expr * expr list * env
  | E_QCallFun of value * expr list * env
  | E_QCallArgs of value * value * value list * expr list * env
  | E_Receive of clause list * expr * env       (* clauses, timeout body, environment *)
  | E_PrimOp of atom * value list * expr list * env
  | E_Try of var_name list * expr * var_name list * expr * env
  | E_Do of expr list * env                     (* technically syntax sugar, but cleaner to handle directly *)
  | E_Catch
  (* Map construction frames.  Evaluation order: key-value pairs left-to-right,
     then the base map expression last.  The saved [env] restores the outer
     environment when the frame is popped. *)
  | E_MapKey of (Syntax.Core_ast.map_assoc_op * value * value) list  (* pairs evaluated so far *)
              * Syntax.Core_ast.map_assoc_op                          (* current pair's op *)
              * Syntax.Core_ast.expr                                  (* current pair's val-expr *)
              * Syntax.Core_ast.map_assoc list                        (* remaining pairs *)
              * Syntax.Core_ast.expr option                           (* base expr, if any *)
              * env
  | E_MapVal of (Syntax.Core_ast.map_assoc_op * value * value) list
              * value                                                  (* evaluated key *)
              * Syntax.Core_ast.map_assoc_op
              * Syntax.Core_ast.map_assoc list
              * Syntax.Core_ast.expr option
              * env
  | E_MapBase of (Syntax.Core_ast.map_assoc_op * value * value) list  (* all pairs done; apply to base *)
               * env
  | E_Ets of ets_op   (* scheduler-resolved ETS operation; see notes/ets_plan.md *)
[@@deriving sexp_of]

(** A pending ETS operation, validated by [Ets_bifs.dispatch] and resolved by
    the scheduler (maximise for forced/producer cases, schedule for observers).
    Carried both in [SR_Ets] (for immediate resolution) and in the [E_Ets]
    frame, so a settled process re-emits the same [Stuck] when re-stepped --
    exactly like [E_Receive].  [elem = Some pos] marks [lookup_element/3]. *)
and ets_op =
  | Ets_new    of { tname : atom; named : bool }
  | Ets_insert of { tab : value; obj : value }
  | Ets_lookup of { tab : value; key : value; elem : int option }
  | Ets_delete of { tab : value }
[@@deriving sexp_of]

type eval_cxt = eval_frame list [@@deriving sexp_of]

type inner_term =
  | T_Expr  of expr
  | T_Vals  of value_seq
  | T_Raise of raised_exception
[@@deriving sexp_of]

type cek_term = {
    ecxt : eval_cxt;
    term : inner_term
  }
[@@deriving sexp_of]

(** Commit clock (restricted vector clock; see [notes/vector_clocks_plan.md],
    plus the later send/ref/ETS extensions in [notes/ref_creation_order_plan.md]
    and [notes/ets_plan.md]).
    A sparse vector [pid -> int]; only process [r] increments component [r].
    Producer events (send, make_ref, ETS new/write/delete, owner-exit table
    death) bump their own component and stamp the produced artifact.  Observer
    events (receive, ETS lookup/badarg-on-death) join the observed stamp and
    then bump; empty ETS lookups bump as observation events so their absence
    anti-dependencies can be recorded.  Spawns copy the parent's clock; timeouts
    do not bump.  Absent key = 0. *)
type clock = int PidMap.t

let sexp_of_clock (c : clock) = PidMap.sexp_of_t sexp_of_int c

(** [clock_get r c] is component [r] of [c] (0 if absent). *)
let clock_get (r : pid) (c : clock) : int =
  match PidMap.find_opt r c with Some n -> n | None -> 0

(** Pointwise max. *)
let clock_join (a : clock) (b : clock) : clock =
  PidMap.union (fun _ x y -> Some (max x y)) a b

(** Increment component [r]. *)
let clock_bump (r : pid) (c : clock) : clock =
  PidMap.add r (clock_get r c + 1) c

(** [clock_leq a b]: [a] happens-before-or-equals [b] (pointwise <=). *)
let clock_leq (a : clock) (b : clock) : bool =
  PidMap.for_all (fun p n -> n <= clock_get p b) a

type deferred_receive = {
    srcs    : pid list;
    timeout : bool;
  }
[@@deriving sexp_of]

type deferred =
  | Deferred_receive of deferred_receive
  | Deferred_ets_write
      (** Non-owner insert that declined success-now.  Success-later is
          identical to success-now (the frozen writer's clock cannot change),
          so on a later tombstone the only remaining outcome is forced badarg.
          See notes/ets_plan.md (deferred-op scheme). *)
  | Deferred_ets_lookup of { seen : (pid * int) list; nil_offered : bool }
      (** Lookup that declined the current alternatives.  [seen] is the
          per-writer channel length already offered (only later writes may be
          returned on wake); [nil_offered] records that the [] branch was
          offered (never re-offered: [] later is identical to [] now). *)
[@@deriving sexp_of]

type process_conf = {
    pid          : pid;
    cek          : cek_term;
    env          : env;
    deferred     : deferred option;
    pdict        : (value * value) list;
    clock        : clock;
  }
[@@deriving sexp_of]

(* -------------------------------------------------------------------- *)
(* Layer 1 (Network) -- scheduler                                         *)
(* -------------------------------------------------------------------- *)

(** A fixed peer-to-peer FIFO pipe between one sender and one receiver
    (CFSMs, Brand & Zafiropulo 1983).  Channels represent the *aether*:
    messages that have been sent but whose delivery is scheduled by the
    scheduler, so a message in a channel may still experience delay before
    it reaches the receiver.  Per-sender channels make cross-sender
    independence structural: the checker branches only when a receive has
    multiple channels with a first matching message, which is exactly the
    condition under which optimal DPOR with observers (Aronis et al. 2018)
    would branch (observer set O != {}).  The src/dst pids are encoded as
    map keys in [network_conf] rather than stored here.

    Each message carries a [same_sender_visible] flag.  A message becomes
    same-sender-visible when a [scan_channel] call passes over it without matching
    in order to receive a later message from the same sender.  In that branch,
    the later message has been delivered, so by same-sender FIFO the earlier
    message must already be in the receiver's mailbox.  The scheduler uses this
    flag to distinguish same-sender-forced visible messages from in-flight channel
    messages.  A matching same-sender-visible message suppresses timeout/delay
    branches; a nonmatching one does not.

    Clocks ([notes/vector_clocks_plan.md]): [send_clock] is a snapshot of the
    sender's commit clock at send time.  The flag carries the receiver's
    post-commit clock from the commit that skipped the message ([Some c]);
    first flag wins -- a later skip keeps the original stamp, which is the
    strongest fact (the message was in the mailbox at least that early). *)
type message = {
    value               : value;
    send_clock          : clock;
    same_sender_visible : clock option;
  }
[@@deriving sexp_of]

type channel = {
    msgs : message list;  (* front = oldest; FIFO per sender *)
  }
[@@deriving sexp_of]

(** Reason a process became [Stuck]: waiting on a network action that the
    Layer 0 reducer cannot resolve alone. *)
type stuck_reason =
  | SR_Receive of { clauses      : clause list
                  ; timeout      : value
                  ; timeout_body : expr
                  ; rho          : env
                  ; cont         : eval_cxt }
  | SR_Send    of { dst : pid; msg : value }
  | SR_Spawn   of { clo : closure; args : value list; cont : eval_cxt }
  | SR_Ets     of { op : ets_op; cont : eval_cxt }
[@@deriving sexp_of]

type 'a status =
  | Running of 'a list
  | Done    of 'a
  | Stuck   of stuck_reason * 'a
[@@deriving sexp_of]

(** The network configuration: all live processes and the pairwise
    channels carrying their messages in transit.  "Network" in the sense
    of CCS (Milner 1980) -- a parallel composition of named agents.
    The channels model two things at once: the aether where messages live
    between send and receive, and the delivery schedule that the network
    driver controls for exhaustive exploration.
    Indexed [channels.(dst).(src)]. *)
type ref_env = {
    order   : (int * int) list;  (* ordering constraints: fst < snd *)
    next_id : int;               (* counter for fresh ref IDs *)
    stamps  : (int * (pid * clock)) list;
      (* ref id -> (creator pid, creator's clock after the make_ref bump);
         see [notes/ref_creation_order_plan.md] *)
  }
[@@deriving sexp_of]

let empty_ref_env = { order = []; next_id = 0; stamps = [] }

(** [creation_order refs a b] consults the creation stamps of refs [a] and [b]
    and reports their causal creation order:
    - [Some true]  -- a's creation happens-before b's: a < b is forced.
    - [Some false] -- b's creation happens-before a's: b < a is forced.
    - [None]       -- concurrent (or a stamp is missing): order undetermined,
                      so a comparison must branch on both orderings.
    Exact by single-writer freshness: only the creator increments its own
    component, and the make_ref bump makes each creation a distinct event, so
    [cb[pa] >= ca[pa]] holds iff b's creator observed a's creation. *)
let creation_order (refs : ref_env) (a : int) (b : int) : bool option =
  match List.assoc_opt a refs.stamps, List.assoc_opt b refs.stamps with
  | Some (pa, ca), Some (pb, cb) ->
     if clock_get pa cb >= clock_get pa ca then Some true
     else if clock_get pb ca >= clock_get pb cb then Some false
     else None
  | _ -> None

(* -------------------------------------------------------------------- *)
(* ETS shared state (notes/ets_plan.md)                                  *)
(* -------------------------------------------------------------------- *)

(** One completed key-write event: the inserted object and the writer's clock
    at the commit (post-bump).  Not a delivery-queue message. *)
type ets_write = { obj : value; wclock : clock }
[@@deriving sexp_of]

(** One table.  [writes] holds per-(key, writer) channels, oldest first --
    ALL of the writer's events; channels are never shortened.
    Read coherence is clock-based (see
    [Scheduler.schedule_ets]/[Scheduler.make_successor]): a write is stale for a
    reader iff a strictly-newer same-key write is already forced ([<= Cr]) for
    that reader.  One reader's choice never deletes evidence for a concurrent
    reader.  Anti-dependency ordering that staleness alone does not force (a
    read of a newer value is after every read of an older one) is carried by
    the forced-order graph's RW edges, not by clocks: the observation stamps
    that used to fold it into read clocks ([observed_at] per write,
    [nil_observed_at] per key) were retired 2026-07-25 once the graph was
    measured to derive the same orderings -- see [Forced_order] and
    `notes/forced_order_handover.md` R1.
    [dead = Some c] is the table-wide lifecycle tombstone (owner delete or owner
    exit, clock [c]); write channels are retained after death because lookups
    concurrent with the death may still order themselves before it. *)
type ets_table = {
    tid      : int;
    et_owner : pid;
    et_name  : atom option;                        (* Some n for named tables *)
    dead     : clock option;                       (* tombstone; None = live *)
    writes   : ((value * pid) * ets_write list) list;  (* (key, writer) -> events *)
  }
[@@deriving sexp_of]

(** Scheduler-owned ETS state: shared data, not a table-server process.
    [names] holds only live bindings (unbound at table death).  Table ids are
    allocated from [ref_env.next_id] (tids are references, with creation
    stamps), so there is no separate counter here. *)
type ets_state = {
    tables   : ets_table list;
    names    : (atom * int) list;
  }
[@@deriving sexp_of]

let empty_ets_state = { tables = []; names = [] }

(* -------------------------------------------------------------------- *)
(* Forced-order graph (notes/forced_order_graph_plan.md)                 *)
(* -------------------------------------------------------------------- *)

(** An observation-relevant event after it happens, named by its process and
    own tick post-bump.  The bump invariant makes the name per-path unique:
    every event recorded here has advanced its process's own clock entry. *)
type fo_node = pid * int
[@@deriving sexp_of]

(** Event kinds.  ETS writes and reads (value and nil), sends, and fired
    receives.  A fired receive retains its matcher -- the clause list and
    environment [schedule_deliveries] matched with -- so a later send can be
    tested against it (the retroactive first-match rule, plan §4.4). *)
type fo_event =
  | Fo_write of { fo_tid : int; fo_key : value }
  | Fo_read  of { fo_tid : int; fo_key : value
                ; fo_from : fo_node option }   (* rf: the write read; None = nil *)
  | Fo_send  of { fo_dst : pid }               (* the message; its arrival is implicit *)
  | Fo_recv  of { fo_dst : pid                 (* = the receiver's pid *)
                ; fo_consumed : fo_node        (* the consumed message's send node *)
                ; fo_clauses : clause list     (* retained matcher... *)
                ; fo_env : env }               (* ...with its bindings *)
[@@deriving sexp_of]

module FoNodeKey = struct
  type t = fo_node
  let compare = compare
  let sexp_of_t = sexp_of_fo_node
end

module FoNodeMap = MakeSexpOfMap(FoNodeKey)

module FoNodeSet = struct
  include Set.Make(FoNodeKey)
  let sexp_of_t s = [%sexp_of: FoNodeKey.t list] (elements s)
end

module TickKey = struct
  type t = int
  let compare = compare
  let sexp_of_t = sexp_of_int
end

module TickMap = MakeSexpOfMap(TickKey)

(** The recorded forced-order state for one exploration path, keyed the way
    reachability queries it (the [channels.(dst).(src)] treatment):

    [fo_events] nests process -> tick -> (kind, commit clock), so a
    process's events form a tick-ordered map: the hb and fifo steps of
    [Forced_order.reachable_position] become per-process suffix walks (clock
    clock entries are monotone along a process's events) instead of scans of
    the whole graph.  [fo_edges] (recorded RW/WW, between events) and
    [fo_arr_edges] (recorded fm, both endpoints send nodes, meaning arrival
    order [Arr(a) < Arr(b)], usable only through the bridge discipline,
    plan §5) map each source to its targets.  [fo_edges] targets are a SET:
    [saturate]'s recorded-edge guard is a membership test on the innermost
    path, and RW out-degrees grow along write-heavy paths, so they must not
    be a scanned list.  [fo_arr_edges] targets stay a LIST: no membership
    test exists there (fm duplicates are structurally impossible -- sources
    are consumed-once messages, retroactive targets fresh sends), the only
    use is iteration, and a cons is cheaper than a set node on the
    fm-heavy path.
    [fo_consumer] maps a consumed message's send node to the fired receive
    that consumed it (at most one per path) -- the consume bridge as a
    lookup.  po/hb edges are implicit (derived from clocks), rf is hb
    already (the read's clock joins the write's clock), and same-sender
    fifo arrival order is implicit in send-node ticks, so none of those are
    recorded.  See [Forced_order]. *)
type fo_graph = {
    fo_events    : (fo_event * clock) TickMap.t PidMap.t;
    fo_edges     : FoNodeSet.t FoNodeMap.t;
    fo_arr_edges : fo_node list FoNodeMap.t;
    fo_consumer  : fo_node FoNodeMap.t;
  }
[@@deriving sexp_of]

let empty_fo_graph = { fo_events = PidMap.empty
                     ; fo_edges = FoNodeMap.empty
                     ; fo_arr_edges = FoNodeMap.empty
                     ; fo_consumer = FoNodeMap.empty }

type network_conf = {
    processes : process_conf list;
    channels  : channel PidMap.t PidMap.t;  (* channels.(dst).(src) *)
    next_pid  : pid;
    refs      : ref_env;
    ets       : ets_state;
    fo        : fo_graph;
  }
[@@deriving sexp_of]

(* -------------------------------------------------------------------- *)
(* CEK stepping utilities                                                *)
(*                                                                       *)
(* Shared by all BIF dispatch modules (erlang_bifs, primops, io_bifs).  *)
(* -------------------------------------------------------------------- *)

let return_val (conf : process_conf) (rest : eval_cxt) (v : value)
    : process_conf status =
  Running [{ conf with cek = { ecxt = rest; term = T_Vals [v] } }]

let return_vals (conf : process_conf) (rest : eval_cxt) (vs : value list)
    : process_conf status =
  Running [{ conf with cek = { ecxt = rest; term = T_Vals vs } }]

let raise_exn (conf : process_conf) (rest : eval_cxt)
    (class_ : exception_class) (reason : value)
    : process_conf status =
  let ex = { class_; reason; info = V_nil } in
  Running [{ conf with cek = { ecxt = rest; term = T_Raise ex } }]

(** Lift a plain [process_conf status] into a [(ref_env * process_conf) status]
    by pairing each conf with the given [refs].  Used at BIF dispatch call sites
    where the BIF does not modify [refs]. *)
let lift_refs (refs : ref_env) : process_conf status -> (ref_env * process_conf) status = function
  | Running cs   -> Running (List.map (fun c -> (refs, c)) cs)
  | Done c       -> Done (refs, c)
  | Stuck (r, c) -> Stuck (r, (refs, c))
