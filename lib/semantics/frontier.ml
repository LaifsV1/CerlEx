(** Exploration frontier: the worklist of pending configurations, together with
    the search discipline ([BFS]/[DFS]) that governs both this worklist and the
    order processes are enqueued during [maximise].  Factored out of
    [scheduler.ml]; fully polymorphic, with no dependency on scheduler
    internals. *)

(** [BFS]: append to the worklist / [pending] (queue); [DFS]: prepend (stack). *)
type search_order = BFS | DFS

let search_order : search_order ref = ref DFS
(** DFS by default: bounds the frontier (BFS can grow it to GBs); [-bfs] selects BFS *)

(** Functional 2-list queue.  [front] holds items ready to dequeue (head =
    next item); [back] holds recently enqueued items in reverse order (each
    enqueue is a cons onto [back]).  When [front] is empty, [back] is
    reversed into [front].  [size] is kept for O(1) [frontier_size]. *)
type 'a frontier = { front : 'a list; back : 'a list; size : int }

let empty_frontier : 'a frontier = { front = []; back = []; size = 0 }

let frontier_is_empty q = q.size = 0

let frontier_size q = q.size

let frontier_pop q =
  match q.front with
  | x :: front -> (x, { q with front; size = q.size - 1 })
  | [] ->
    match List.rev q.back with
    | []         -> failwith "frontier_pop: empty"
    | x :: front -> (x, { front; back = []; size = q.size - 1 })

(** BFS: enqueue [xs] onto the back (cons each item; O(|xs|) tail-recursive).
    DFS: push [xs] onto the front (same cons fold, just onto [front]). *)
let frontier_add (xs : 'a list) (q : 'a frontier) : 'a frontier =
  let size = q.size + List.length xs in
  match !search_order with
  | BFS -> { q with back  = List.rev_append xs q.back;  size }
  | DFS -> { q with front = List.rev_append xs q.front; size }
