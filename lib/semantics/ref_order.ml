(** Constraint graph over symbolic reference IDs.

    Edges are stored as [(int * int) list] where [(a, b)] means [a < b].
    The graph is always a DAG: [add_constraint] rejects edges that would
    create a cycle.  [reaches] is a plain DFS; no visited set is needed
    since the DAG invariant guarantees termination.

    @author Yu-Yang Lin
 *)

type order = (int * int) list

(** [reaches order src dst] is [true] iff [dst] is reachable from [src]
    by following edges in [order]. *)
let rec reaches (order : order) (src : int) (dst : int) : bool =
  src = dst ||
  List.exists (fun (a, b) -> a = src && reaches order b dst) order

(** [add_constraint order a b] attempts to record [a < b].
    Returns [Some order] unchanged if [a] already reaches [b] (constraint already
    present or implied by transitivity -- avoids duplicate edges).
    Returns [None] if [b] already reaches [a] (adding would create a cycle).
    Returns [Some order'] with [(a, b)] prepended otherwise. *)
let add_constraint (order : order) (a : int) (b : int) : order option =
  if reaches order a b then Some order
  else if reaches order b a then None
  else Some ((a, b) :: order)
