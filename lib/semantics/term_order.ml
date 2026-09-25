(** Erlang total term order and structural equality.

    Extracted from [Erlang_bifs] so that [Maps_bifs] and any future module
    that needs to compare or sort [value]s can import this without depending
    on the full BIF dispatch.

    Erlang total term order (number < atom < fun < pid < tuple < map < list < binary):
    used by the comparison operators [<], [>], [=<], [>=] and by map key sorting.
 *)

open Ast

(* -------------------------------------------------------------------- *)
(* Erlang term total order                                               *)
(*                                                                       *)
(* Erlang defines a total ordering across all value types, used by the  *)
(* comparison operators <, >, =<, >=:                                    *)
(*   number < atom < fun < pid < tuple < map < list < binary            *)
(* type_rank maps each constructor to its position in this ordering.    *)
(* Same-type comparisons fall through to type-specific logic below.     *)
(* -------------------------------------------------------------------- *)

let type_rank = function
  | V_int _ | V_float _ | V_char _ -> 0
  | V_atom _    -> 1
  | V_ref _ | V_ets_tid _ -> 2   (* tids are references on BEAM (OTP 22+) *)
  | V_closure _ -> 3
  | V_pid _     -> 4
  | V_tuple _   -> 5
  | V_map _     -> 6
  | V_nil | V_cons _ -> 7
  | V_binary _  -> 8

let numeric_value = function
  | V_int n   -> Z.to_float n
  | V_float f -> f
  | V_char c  -> float_of_int (Char.code c)
  | _ -> assert false

let rec erlang_compare v1 v2 =
  let r1 = type_rank v1 and r2 = type_rank v2 in
  if r1 <> r2 then Int.compare r1 r2
  else
    match v1, v2 with
    | (V_int _ | V_float _ | V_char _), _ ->
       Float.compare (numeric_value v1) (numeric_value v2)
    | V_atom a1, V_atom a2 ->
       String.compare a1 a2
    | V_ref r1, V_ref r2 ->
       Int.compare r1 r2
    | V_ets_tid t1, V_ets_tid t2 ->
       Int.compare t1 t2
    (* Mixed kind: BEAM's cross-kind order is implementation-defined
       (measured: ordinary refs < tids).  Program-level mixed ORDERING kills
       the exploration in [Erlang_bifs.dispatch_r] before reaching here; this
       arm serves internal total-order uses only (e.g. map-key sorting).
       Known liberty: a map keyed by both a ref and a tid would expose this
       order via maps:to_list. *)
    | V_ref _, V_ets_tid _ -> -1
    | V_ets_tid _, V_ref _ -> 1
    | V_closure _, V_closure _ ->
       0  (* undefined; closures have no canonical order *)
    | V_pid p1, V_pid p2 ->
       Int.compare p1 p2
    | V_tuple vs1, V_tuple vs2 ->
       let c = Int.compare (List.length vs1) (List.length vs2) in
       if c <> 0 then c else List.compare erlang_compare vs1 vs2
    | V_map kvs1, V_map kvs2 ->
       let c = Int.compare (List.length kvs1) (List.length kvs2) in
       if c <> 0 then c
       else List.compare (fun (k1,v1) (k2,v2) ->
                let c = erlang_compare k1 k2 in
                if c <> 0 then c else erlang_compare v1 v2)
              kvs1 kvs2
    | V_nil,  V_nil    -> 0
    | V_nil,  V_cons _ -> -1
    | V_cons _, V_nil  -> 1
    | V_cons (h1, t1), V_cons (h2, t2) ->
       let c = erlang_compare h1 h2 in
       if c <> 0 then c else erlang_compare t1 t2
    | V_binary (b1, l1), V_binary (b2, l2) ->
       let c = compare l1 l2 in
       if c <> 0 then c else Z.compare b1 b2
    | _ -> assert false

(* [==] / [/=]: numeric equality coerces int and float (1 == 1.0 is true).
   [=:=] / [=/=] use exact structural equality (1 =:= 1.0 is false). *)
let erlang_num_eq v1 v2 =
  match v1, v2 with
  | (V_int _ | V_float _ | V_char _), (V_int _ | V_float _ | V_char _) ->
     Float.equal (numeric_value v1) (numeric_value v2)
  | _ -> v1 = v2

(* Closures use physical equality: same allocation = same object (F =:= F is true);
   separate allocations = distinct closures (make() =:= make() is false).
   Compound types recurse so closures nested inside tuples/cons/maps are handled. *)
let rec erlang_exact_eq v1 v2 = match v1, v2 with
  | V_closure _, V_closure _          -> v1 == v2
  | V_tuple vs1, V_tuple vs2          -> List.equal erlang_exact_eq vs1 vs2
  | V_cons (h1, t1), V_cons (h2, t2) -> erlang_exact_eq h1 h2 && erlang_exact_eq t1 t2
  | V_map kvs1, V_map kvs2           ->
     List.equal (fun (k1,v1) (k2,v2) -> erlang_exact_eq k1 k2 && erlang_exact_eq v1 v2)
       kvs1 kvs2
  | _                                 -> v1 = v2
