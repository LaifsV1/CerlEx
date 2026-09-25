(** Forced-order graph: cycle rejection for jointly-unrealisable observation
    assignments (notes/forced_order_graph_plan.md; formal statement in
    notes/observation_semantics.tex, "Joint consistency").

    The schedule phase enumerates observation assignments whose individual
    branches are locally enabled; their combination can still be cyclic.
    Clocks cannot carry the missing constraints: they are upper bounds such
    as "this read precedes that concurrent event", and the target may have
    happened in an earlier round with an immutable clock.  This module
    records those forced edges explicitly, including retroactive edges in
    either temporal direction, and reports a cycle, whereupon the scheduler
    drops the successor -- the [Ref_order.add_constraint] precedent, for
    event order.

    Every edge is a fact about any linearisation realising the path's
    assignment, so only unrealisable classes are pruned.  Deliberately
    outside the relation: unobserved same-key write-write order and
    unobserved cross-sender arrival order (the [UWO] collapse and
    asynchronous transport are quotients to preserve).

    Two instances: RW/WW edges over ETS write/read events (plan §4.1-§4.2),
    and fm (first-match) arrival edges over send/receive events (§4.3-§4.4).
    The graph type ([Ast.fo_graph]) lives in [ast.ml] so [canonical.ml] can
    serialise it; the algorithms live here, following the
    [ref_order.ml]/[trace.ml]/[frontier.ml] factoring.  The matcher test
    behind fm edges stays in the scheduler (it needs clause selection and
    the module table); the scheduler hands this module ready-made edges. *)

open Ast

(** Forced-order consistency checking, on by default; [-no-fo] clears it.

    When off, every recording entry point below returns its graph unchanged
    and no cycle is ever reported, so the graph stays empty and no branch
    vector is ever rejected on forced-order grounds.  That restores the
    pre-graph behaviour, which is {e explicitly over-approximating}: the
    joint-consistency witnesses regress to their pre-graph counts and the
    reported trace counts are known to be too high.  Unlike [-no-sleep] and
    [-no-gc], which are performance switches that leave counts unchanged,
    this one deliberately changes the answer -- it exists for A/B measurement
    against the graph (notes/forced_order_handover.md). *)
let enabled : bool ref = ref true

let node_str ((p, t) : fo_node) : string = Printf.sprintf "%d:%d" p t

let find_event (g : fo_graph) ((p, t) : fo_node) : (fo_event * clock) option =
  match PidMap.find_opt p g.fo_events with
  | None -> None
  | Some ts -> TickMap.find_opt t ts

(* RW/WW edges: target sets (membership-tested by [saturate]'s guard). *)
let edge_targets (edges : FoNodeSet.t FoNodeMap.t) (n : fo_node) : FoNodeSet.t =
  match FoNodeMap.find_opt n edges with
  | Some s -> s
  | None -> FoNodeSet.empty

let record_edge_unchecked
    (edges : FoNodeSet.t FoNodeMap.t) (a : fo_node) (b : fo_node)
    : FoNodeSet.t FoNodeMap.t =
  FoNodeMap.update a (function None -> Some (FoNodeSet.singleton b)
                             | Some s -> Some (FoNodeSet.add b s)) edges

(** [edge_recorded edges a b]: the edge [a -> b] is explicitly recorded.
    A duplicate guard, not a reachability test -- O(log) at both levels. *)
let edge_recorded
    (edges : FoNodeSet.t FoNodeMap.t) (a : fo_node) (b : fo_node) : bool =
  FoNodeSet.mem b (edge_targets edges a)

(* fm arrival edges: target lists (iterated only; no membership test, and
   duplicates are structurally impossible per path). *)
let arrival_edge_targets
    (edges : fo_node list FoNodeMap.t) (n : fo_node) : fo_node list =
  match FoNodeMap.find_opt n edges with
  | Some l -> l
  | None -> []

let record_arrival_edge_unchecked
    (edges : fo_node list FoNodeMap.t) (a : fo_node) (b : fo_node)
    : fo_node list FoNodeMap.t =
  FoNodeMap.update a (function None -> Some [b] | Some l -> Some (b :: l)) edges

(** Record an event after it happens.  Every recorded event has bumped its
    process's own clock entry, so [n]'s tick is fresh and a duplicate node
    is a bookkeeping bug, never a silent merge.  A receive that fires also
    indexes itself under the send node it consumed (a message is consumed at
    most once per path -- likewise asserted). *)
let record_event (g : fo_graph) ((p, t) as n : fo_node) (ev : fo_event) (c : clock)
    : fo_graph =
  if not !enabled then g else
  let ts = match PidMap.find_opt p g.fo_events with
    | Some ts -> ts
    | None -> TickMap.empty in
  if TickMap.mem t ts then
    failwith (Printf.sprintf
      "[forced_order] internal: duplicate node %s (bump invariant violated)"
      (node_str n))
  else
    let g = { g with fo_events = PidMap.add p (TickMap.add t (ev, c) ts) g.fo_events } in
    match ev with
    | Fo_recv { fo_consumed; _ } ->
       if FoNodeMap.mem fo_consumed g.fo_consumer then
         failwith (Printf.sprintf
           "[forced_order] internal: send node %s consumed twice"
           (node_str fo_consumed))
       else { g with fo_consumer = FoNodeMap.add fo_consumed n g.fo_consumer }
    | Fo_write _ | Fo_read _ | Fo_send _ -> g

(** A position in the relation: at an event, or at the arrival pseudo-node
    of a sent message (named by its send node).  Arrival nodes are never
    materialised in the graph; they exist only as DFS positions, which is
    exactly the bridge discipline of plan §5. *)
type fo_position = Ev of fo_node | Arr of fo_node

module FoPositionSet = Set.Make(struct
  type t = fo_position
  let compare = compare
end)

(** The positions reachable in one step from [position].  Kept separate from
    the DFS so schedule-local fm checks can compute the parent's reachability
    once while ordinary cycle checks retain their early exit. *)
let outgoing_positions (g : fo_graph) (position : fo_position)
    : fo_position list =
  match position with
  | Ev ((p, t) as n) ->
     let recorded =
       FoNodeSet.fold (fun m acc -> Ev m :: acc) (edge_targets g.fo_edges n) [] in
     let hb =
       PidMap.fold (fun q ts acc ->
         let seq =
           if q = p then TickMap.to_seq_from (t + 1) ts
           else TickMap.to_seq ts in
         match Seq.find (fun (_, (_, c)) -> clock_get p c >= t) seq with
         | Some (s, _) -> Ev (q, s) :: acc
         | None -> acc
       ) g.fo_events [] in
     let bridge = match find_event g n with
       | Some (Fo_send _, _) -> [Arr n]
       | _ -> [] in
     List.rev_append bridge (List.rev_append recorded hb)
  | Arr ((p, t) as n) ->
     let dst = match find_event g n with
       | Some (Fo_send { fo_dst }, _) -> fo_dst
       | _ ->
          failwith (Printf.sprintf
            "[forced_order] internal: arrival position at non-send node %s"
            (node_str n)) in
     let recorded =
       List.rev_map (fun m -> Arr m) (arrival_edge_targets g.fo_arr_edges n) in
     let fifo =
       match PidMap.find_opt p g.fo_events with
       | None -> []
       | Some ts ->
          let is_send_to_dst (_, (ev, _)) = match ev with
            | Fo_send { fo_dst = d' } -> d' = dst
            | _ -> false in
          begin match Seq.find is_send_to_dst (TickMap.to_seq_from (t + 1) ts) with
          | Some (s, _) -> [Arr (p, s)]
          | None -> []
          end in
     let consume = match FoNodeMap.find_opt n g.fo_consumer with
       | Some r -> [Ev r]
       | None -> [] in
     List.rev_append consume (List.rev_append recorded fifo)

(** [reachable_position g a b]: [b] is in the forced future of [a], reflexively.
    DFS over the recorded edges plus the implicit steps:

    - hb (from [Ev (p,t)]): to [Ev (q,s)] when the recorded commit clock of
      [(q,s)] has its [p] entry at least [t] -- exact by single-writer
      freshness (only [p] advances its own clock entry, and each bump is a
      distinct event, so the entry reaches [t] only by observing [(p,t)]).
      For [q = p]
      this is exactly program order, so po needs no separate step.
    - send bridge: [Ev n -> Arr n] when [n] is a send ([send(x) < Arr(x)]).
    - recorded arrival (fm) edges: [Arr x -> Arr y].
    - fifo (implicit arrival edges): [Arr (p,t) -> Arr (p,t')] for sends of
      the same sender to the same destination with [t' > t].
    - consume bridge: [Arr m -> Ev r] when fired receive [r] consumed [m]
      ([Arr(m) < consume(m)]).

    There is deliberately no step from [Arr n] into [Ev n]'s po/hb
    successors: arrival says nothing about the sender's later events.

    The implicit steps are narrowed to one successor per process, with the
    same transitive closure: for hb, only the FIRST event of each process
    [q] whose clock has its [p] entry at least [t] -- clock entries are
    monotone along a process's events (tick order is time order), so [q]'s later
    qualifying events are reachable from that first one by po; for fifo,
    only the FIRST later same-sender send to the destination -- subsequent
    ones are reachable from its arrival by the same fifo step.  The
    ascending walk stops at the first hit for the same monotonicity
    reason. *)
let reachable_position (g : fo_graph) (a : fo_position) (b : fo_position) : bool =
  (* Per-query seen set as a functional set: the empty set is a shared
     constant (nothing allocated per query), membership is O(log k), and
     adding one member allocates only the rebalancing path -- ties the list at the
     shallow depths of the fm cycle checks, wins at the deep depths of the
     ETS saturation queries.  (A per-query hashtable was measured and
     rejected: its allocation/init constants lose at shallow depth --
     notes/forced_order_todo.md.) *)
  let rec dfs visited = function
    | [] -> false
    | position :: rest ->
       if position = b then true
       else if FoPositionSet.mem position visited then dfs visited rest
       else
         dfs (FoPositionSet.add position visited)
           (List.rev_append (outgoing_positions g position) rest)
  in
  dfs FoPositionSet.empty [a]

(** Event-order reachability (both endpoints as events). *)
let reachable (g : fo_graph) (a : fo_node) (b : fo_node) : bool =
  reachable_position g (Ev a) (Ev b)

(** Parent-graph reachability among the arrival positions of a fixed set of
    send nodes.  A schedule point computes this once, before sibling branch
    vectors extend the parent graph.

    [reachability_bits] contains both directions of the relation: the first
    [endpoint_count] rows are "reachable from", and the next
    [endpoint_count] rows are "can reach".  Rows are packed into OCaml
    integers so the common alltoall7 case (42 endpoints) occupies one word
    per row.  A schedule point keeps the whole relation in one flat array
    and resets one scratch array before each branch vector, rather than
    rebuilding maps and sets for every fm edge. *)
type parent_reachability =
  { endpoint_index : (fo_node, int) Hashtbl.t
  ; endpoint_count : int
  ; words_per_row : int
  ; reachability_bits : int array
  }

(** Mutable schedule-local scratch for one branch vector's relation.  It is
    reset to the parent relation before each branch vector and never enters
    the configuration. *)
type branch_vector_reachability = int array

(* Reserve the sign bit so every packed word stays nonnegative; the
   low-bit scan below can then use subtraction and logical shifts portably. *)
let bits_per_word = Sys.int_size - 1

let row_offset (parent : parent_reachability) (index : int) : int =
  index * parent.words_per_row

let reverse_row_offset (parent : parent_reachability) (index : int) : int =
  (parent.endpoint_count + index) * parent.words_per_row

let set_bit (bits : int array) (offset : int) (index : int) : unit =
  let word = index / bits_per_word in
  let mask = 1 lsl (index mod bits_per_word) in
  bits.(offset + word) <- bits.(offset + word) lor mask

let bit_is_set (bits : int array) (offset : int) (index : int) : bool =
  let word = index / bits_per_word in
  let mask = 1 lsl (index mod bits_per_word) in
  bits.(offset + word) land mask <> 0

let endpoint_index (parent : parent_reachability) (n : fo_node) : int =
  try Hashtbl.find parent.endpoint_index n with
  | Not_found ->
     failwith (Printf.sprintf
       "[forced_order] internal: send node %s absent from parent reachability"
       (node_str n))

(** [parent_reachability g send_nodes] computes, for every send node in
    [send_nodes], which arrival positions in the same set are reachable in
    the parent graph [g].  Each row comes from one complete DFS; the search
    continues through endpoint positions so paths through the rest of the
    graph are preserved. *)
let parent_reachability (g : fo_graph) (send_nodes : FoNodeSet.t)
    : parent_reachability =
  (* [-no-fo]: no node was recorded, so an arrival position would hit
     [outgoing_positions]'s non-send assertion.  Nothing consults the relation
     either ([record_arrival_edges_with_parent_reachability] returns at once),
     so hand back an empty one without searching. *)
  if not !enabled then
    { endpoint_index = Hashtbl.create 0
    ; endpoint_count = 0
    ; words_per_row = 0
    ; reachability_bits = [||] }
  else
  let endpoints = Array.of_list (FoNodeSet.elements send_nodes) in
  let endpoint_count = Array.length endpoints in
  let endpoint_index = Hashtbl.create endpoint_count in
  Array.iteri (fun index n -> Hashtbl.add endpoint_index n index) endpoints;
  let words_per_row =
    if endpoint_count = 0 then 0
    else (endpoint_count + bits_per_word - 1) / bits_per_word in
  let reachability_bits =
    Array.make (2 * endpoint_count * words_per_row) 0 in
  let parent =
    { endpoint_index; endpoint_count; words_per_row; reachability_bits } in
  Array.iteri (fun source_index source ->
    let rec dfs visited = function
      | [] -> ()
      | position :: rest ->
         if FoPositionSet.mem position visited then dfs visited rest
         else
           let visited = FoPositionSet.add position visited in
           begin match position with
           | Arr n ->
              begin match Hashtbl.find_opt endpoint_index n with
              | Some target_index ->
                 set_bit reachability_bits
                   (row_offset parent source_index) target_index;
                 set_bit reachability_bits
                   (reverse_row_offset parent target_index) source_index
              | None -> ()
              end
           | Ev _ -> ()
           end;
           dfs visited (List.rev_append (outgoing_positions g position) rest)
    in
    dfs FoPositionSet.empty [Arr source]
  ) endpoints;
  parent

let branch_vector_reachability (parent : parent_reachability)
    : branch_vector_reachability =
  Array.copy parent.reachability_bits

let reset_branch_vector_reachability (parent : parent_reachability)
    (bits : branch_vector_reachability) : unit =
  Array.blit parent.reachability_bits 0 bits 0
    (Array.length parent.reachability_bits)

let lowest_bit_in_byte =
  Array.init 256 (fun byte ->
    let rec find index =
      if byte land (1 lsl index) <> 0 then index else find (index + 1)
    in
    if byte = 0 then -1 else find 0)

let lowest_bit_index (bits : int) : int =
  let rec find offset remaining =
    let byte = remaining land 0xff in
    if byte <> 0 then offset + lowest_bit_in_byte.(byte)
    else find (offset + 8) (remaining lsr 8)
  in
  find 0 bits

let union_row (parent : parent_reachability) (bits : int array)
    (dst_offset : int) (src_offset : int) : unit =
  for word = 0 to parent.words_per_row - 1 do
    bits.(dst_offset + word) <-
      bits.(dst_offset + word) lor bits.(src_offset + word)
  done

let rec add_after_b_to_predecessors (parent : parent_reachability)
    (bits : int array) (after_b : int) (word : int) (remaining : int) : unit =
  if remaining <> 0 then begin
    let local_index = lowest_bit_index remaining in
    let before_a = word * bits_per_word + local_index in
    union_row parent bits (row_offset parent before_a) after_b;
    add_after_b_to_predecessors
      parent bits after_b word (remaining land (remaining - 1))
  end

let rec add_predecessors_to_after_b (parent : parent_reachability)
    (bits : int array) (predecessors : int) (word : int) (remaining : int)
    : unit =
  if remaining <> 0 then begin
    let local_index = lowest_bit_index remaining in
    let after_b = word * bits_per_word + local_index in
    union_row parent bits (reverse_row_offset parent after_b) predecessors;
    add_predecessors_to_after_b
      parent bits predecessors word (remaining land (remaining - 1))
  end

(** Record [a -> b] in the branch vector's reachability.  The relation is
    kept transitively closed: every endpoint that can reach [a] gains every
    endpoint reachable from [b], in both the forward and reverse rows. *)
let record_branch_vector_reachability (parent : parent_reachability)
    (bits : branch_vector_reachability) (a : int) (b : int) : unit =
  let predecessors = reverse_row_offset parent a in
  let after_b = row_offset parent b in
  (* Since [b] cannot reach [a] (the caller checked), neither source row is
     changed while it is being read by these two passes. *)
  for word = 0 to parent.words_per_row - 1 do
    add_after_b_to_predecessors
      parent bits after_b word bits.(predecessors + word)
  done;
  for word = 0 to parent.words_per_row - 1 do
    add_predecessors_to_after_b
      parent bits predecessors word bits.(after_b + word)
  done

(** Saturation outcome.  ([Stdlib.result] is unusable here: [Ast] shadows
    its [Error] constructor with [exception_class].) *)
type saturation =
  | Saturated of fo_graph
  | Cycle of fo_node * fo_node   (* the new edge that closed a cycle *)

(** Saturate the ETS rules to fixpoint (plan §2, §4.1):

    - RW (anti-dependency): a read [R] of value [V] on [(tid, key)] precedes
      every same-key write [W'] that forcedly supersedes [V]: [R -> W']
      when [W'] is reachable from [V].  Nil is the key's bottom, superseded by
      every same-key write.
    - WW (inferred write-dependency): if [R] read [W], [R'] read [W'], same
      [(tid, key)], [W <> W'], and [R'] is reachable from [R], then [W -> W'].

    Premises are monotone in reachability and the event set is fixed during
    the pass, so the fixpoint is finite and recording-order-independent.
    A pair whose conclusion edge is already recorded dies at a membership
    lookup before any premise DFS runs -- [saturate] runs whenever a relevant
    event is recorded, so almost every rule instance it proposes is one it
    settled earlier, and without this guard each re-proposal paid a
    premise DFS plus an implied-skip DFS (measured: the dominant cost on
    write-heavy rows -- long_chain 203ms pre-graph vs ~1.2s, almost all of
    it here).  There is deliberately no reachability-based implied skip any
    more: a reachable-but-unrecorded edge is recorded on first proposal (paying
    its premise and cycle DFS once, ever), which leaves the closure -- and
    hence every verdict -- unchanged, exactly the [record_arrival_edge] trade;
    recorded edges are not canonicalised.  Termination measure: each pass
    records a strictly new edge (the guard makes re-recording impossible) or
    the fixpoint halts; bounded by the pair count.  [Cycle (a, b)] when
    recording [a -> b] would close a cycle: the assignment is jointly
    unrealisable and the caller drops the successor. *)
let saturate (g : fo_graph) : saturation =
  if not !enabled then Saturated g else
  let (reads, writes) =
    PidMap.fold (fun p ts acc ->
      TickMap.fold (fun t (ev, c) (rs, ws) ->
        match ev with
        | Fo_read { fo_tid; fo_key; fo_from } ->
           (((p, t), fo_tid, fo_key, fo_from) :: rs, ws)
        | Fo_write { fo_tid; fo_key } ->
           (rs, ((p, t), fo_tid, fo_key, c) :: ws)
        | Fo_send _ | Fo_recv _ -> (rs, ws)
      ) ts acc
    ) g.fo_events ([], []) in
  let same_key tid key tid' key' =
    tid = tid' && Term_order.erlang_exact_eq key key' in
  let step (g : fo_graph) : (fo_graph * bool, fo_node * fo_node) Stdlib.result =
    let rw =
      List.concat_map (fun (r, tid, key, from) ->
        List.filter_map (fun (w', tid', key', wclock') ->
          if not (same_key tid key tid' key') then None
          else if edge_recorded g.fo_edges r w' then None
          else match from with
            | None   -> Some (r, w')                    (* nil: bottom *)
            | Some ((wp, wt) as w) ->
               if w <> w'
                  (* Fast path: the source write [w] is process [wp]'s own
                     tick [wt].  Only [wp] advances [wp]'s own clock entry,
                     so [wclock'.(wp) >= wt] means the target write [w']
                     already has this exact source event in its clock -- it
                     is ordered after it.  Ordering that instead runs
                     through recorded WW/mixed edges has no such clock witness
                     and needs the search. *)
                  && (clock_get wp wclock' >= wt || reachable g w w')
               then Some (r, w') else None
        ) writes
      ) reads
    in
    let ww =
      List.concat_map (fun (r1, tid1, key1, from1) ->
        match from1 with
        | None -> []
        | Some w1 ->
           List.filter_map (fun (r2, tid2, key2, from2) ->
             match from2 with
             | None -> None
             | Some w2 ->
                if r1 <> r2 && same_key tid1 key1 tid2 key2 && w1 <> w2
                   && not (edge_recorded g.fo_edges w1 w2)
                   && reachable g r1 r2
                then Some (w1, w2) else None
           ) reads
      ) reads
    in
    List.fold_left (fun acc (a, b) ->
      match acc with
      | Stdlib.Error e -> Stdlib.Error e
      | Stdlib.Ok (g, changed) ->
         (* within-pass duplicate (e.g. two readers proposing one WW edge;
            the candidate lists ran against the pass's starting graph) *)
         if edge_recorded g.fo_edges a b then Stdlib.Ok (g, changed)
         else if reachable g b a then Stdlib.Error (a, b)
         else
           Stdlib.Ok
             ({ g with
                  fo_edges = record_edge_unchecked g.fo_edges a b }, true)
    ) (Stdlib.Ok (g, false)) (List.rev_append rw ww)
  in
  let rec fix g =
    match step g with
    | Stdlib.Error (a, b) -> Cycle (a, b)
    | Stdlib.Ok (g', true)  -> fix g'
    | Stdlib.Ok (g', false) -> Saturated g'
  in
  fix g

(** When one ETS write lands, record its node and saturate.  The RW-backward
    edges (reads whose value this write forcedly supersedes -- the
    retroactive direction no flag can reach) fall out of the saturation.
    A cycle is impossible here: when it lands, the write is a sink
    (no readers yet, no later same-pid events, its fresh bump in nobody's
    clock), so a detected cycle is an internal error, not a prunable world
    (plan §4.2). *)
let record_write (g : fo_graph) (writer : pid) (wclock : clock)
    (tid : int) (key : value) : fo_graph =
  let n = (writer, clock_get writer wclock) in
  let g = record_event g n (Fo_write { fo_tid = tid; fo_key = key }) wclock in
  match saturate g with
  | Saturated g' -> g'
  | Cycle (a, b) ->
     failwith (Printf.sprintf
       "[forced_order] internal: cycle while recording write %s (edge %s -> %s)"
       (node_str n) (node_str a) (node_str b))

(** Record the fm arrival edge [Arr(a) < Arr(b)] (both send nodes); [None]
    when the new edge closes a cycle (checked in arrival positions, per the
    bridge discipline).  Deliberately no implied-edge skip: recording an
    already-reachable edge leaves the closure -- hence every future verdict
    -- unchanged, edges are not canonicalised, and the skip's reachability
    query is the expensive DFS direction (from the consumed message's
    arrival through its consumer into the event-side hb fan-out), paid on
    every edge to save one list cell almost never (cross-sender
    arrival pairs are rarely reachable).  The kept cycle check starts from
    the arrival of an in-flight unconsumed message and is structurally
    shallow.  Contrast [saturate], whose inline implied check is its
    fixpoint termination condition and must stay; and [Ref_order], where
    the skip is load-bearing (the order list is canonicalised and compared
    structurally).  Measured: alltoall6 2018 -> 909ms, alltoall7 61.1 ->
    23.6s, counts identical.  Each [(a, b)] pair
    is proposed at most once per path (sources are consumed-once messages;
    retroactive targets are fresh sends), so redundant recording stays
    bounded by the number of recorded edges. *)
let record_arrival_edge (g : fo_graph) (a : fo_node) (b : fo_node)
    : fo_graph option =
  if not !enabled then Some g
  else if reachable_position g (Arr b) (Arr a) then None
  else
    Some
      { g with
        fo_arr_edges =
          record_arrival_edge_unchecked g.fo_arr_edges a b }

(** Record one send node, then record the retroactive fm edges
    [send(r.consumed) -> send(n)] for the previously fired receives [rs]
    whose retained matcher takes the new message (plan §4.4; the scheduler
    supplies [rs] -- the consumed-send nodes of those receives).  A cycle is
    believed impossible here: the new arrival [Arr(n)] has no successors
    (no later same-sender sends, unconsumed, no recorded edges), so nothing is
    reachable from it -- assert-and-fail loudly per the plan, to be
    downgraded to a drop only if a witness ever fires it. *)
let record_send (g : fo_graph) (sender : pid) (sclock : clock) (dst : pid)
    (rs : fo_node list) : fo_graph =
  let n = (sender, clock_get sender sclock) in
  let g = record_event g n (Fo_send { fo_dst = dst }) sclock in
  List.fold_left (fun g consumed ->
    match record_arrival_edge g consumed n with
    | Some g' -> g'
    | None ->
       failwith (Printf.sprintf
         "[forced_order] internal: cycle while recording send %s (fm edge %s -> %s)"
         (node_str n) (node_str consumed) (node_str n))
  ) g rs

(** Record one receive's schedule-local fm arrival edges using the parent
    reachability shared by sibling branch vectors.
    [branch_vector_reachability] supplies the fm edges already recorded for
    this branch vector; [g] is the full graph that receives each accepted
    edge.  [None] means one of the new edges closes a cycle. *)
let rec record_arrival_edges_with_parent_reachability
    (parent : parent_reachability)
    (branch_vector_reachability : branch_vector_reachability)
    (g : fo_graph)
    (a : fo_node) (a_index : int)
    (targets : fo_node list) (target_indexes : int list) : fo_graph option =
  if not !enabled then Some g else
  match targets, target_indexes with
  | [], [] -> Some g
  | b :: targets, b_index :: target_indexes ->
     if bit_is_set branch_vector_reachability
          (row_offset parent b_index) a_index
     then None
     else begin
       if not (bit_is_set branch_vector_reachability
                 (row_offset parent a_index) b_index)
       then
         record_branch_vector_reachability
           parent branch_vector_reachability a_index b_index;
       let g =
         { g with
           fo_arr_edges =
             record_arrival_edge_unchecked g.fo_arr_edges a b } in
       record_arrival_edges_with_parent_reachability
         parent branch_vector_reachability g a a_index targets target_indexes
     end
  | [], _ :: _ | _ :: _, [] ->
     failwith "[forced_order] internal: fm target indexes are misaligned"
