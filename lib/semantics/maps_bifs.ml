(** Built-in functions for the [maps] module.

    All primitive maps operations are implemented here as OCaml BIFs over
    [V_map of (value * value) list], a sorted association list whose keys are
    maintained in ascending Erlang term order (see [Term_order.erlang_compare]).

    Higher-order functions (fold/3, map/2, filter/2, filtermap/2, foreach/2)
    are implemented by building a Core Erlang [Expr_let] chain that encodes
    the iteration and handing it back to the CEK machine as the next term to
    evaluate.  Values (the closure and kv pairs) are injected into the
    environment under fresh variable names with prefix _MHO_.

    @author Yu-Yang Lin
 *)

open Ast
open Syntax.Core_ast
open Term_order

(* -------------------------------------------------------------------- *)
(* Internal sorted-list helpers                                          *)
(* -------------------------------------------------------------------- *)

let map_lookup k kvs =
  List.find_opt (fun (k2, _) -> erlang_exact_eq k2 k) kvs
  |> Option.map snd

let map_upsert k v kvs =
  let kvs' = List.filter (fun (k2, _) -> not (erlang_exact_eq k2 k)) kvs in
  let rec insert = function
    | [] -> [(k, v)]
    | ((k2, _) as pair) :: rest ->
        if erlang_compare k k2 <= 0 then (k, v) :: pair :: rest
        else pair :: insert rest
  in
  insert kvs'

let map_remove k kvs =
  List.filter (fun (k2, _) -> not (erlang_exact_eq k2 k)) kvs

(* cons-list from a regular OCaml list *)
let to_cons_list vs = List.fold_right (fun v acc -> V_cons (v, acc)) vs V_nil

(* fold a cons-list: returns Ok accumulated_list or Error on non-list tail *)
let rec cons_fold f acc = function
  | V_nil         -> Ok acc
  | V_cons (h, t) -> cons_fold f (f acc h) t
  | _             -> Error ()

(* -------------------------------------------------------------------- *)
(* Higher-order helpers                                                  *)
(* -------------------------------------------------------------------- *)

(* Fresh variable name prefix; unlikely to clash with user-written Core *)
let mho_f     = "_MHO_F"
let mho_k i   = Printf.sprintf "_MHO_K_%d" i
let mho_v i   = Printf.sprintf "_MHO_V_%d" i
let mho_r i   = Printf.sprintf "_MHO_R_%d" i
let mho_a i   = Printf.sprintf "_MHO_A_%d" i
let mho_nv i  = Printf.sprintf "_MHO_NV_%d" i

let extend_env env pairs =
  let vars' = List.fold_left (fun vs (k, v) -> VarMap.add k v vs) env.vars pairs in
  { env with vars = vars' }

let evar x        = Expr_var x
let eatom s       = Expr_literal (Lit_atom s)
let eapply f args = Expr_apply { fn_name = evar f; fn_args = List.map evar args }
let elet x e body = Expr_let { lb_lhs = [x]; lb_expr = e; lb_rhs = body }

let emap_upserts ?(base = None) assocs =
  Expr_map { map_base = base;
             map_assocs =
               List.map (fun (k, v) -> { ma_op = MapAssoc; ma_key = evar k; ma_val = evar v })
                 assocs }

let ecase_bool cond t f =
  Expr_case { case_exp = cond;
              case_pat = [
                { cp_lhs = [Pat_lit (Lit_atom "true")];  cp_guard = eatom "true"; cp_rhs = t };
                { cp_lhs = [Pat_lit (Lit_atom "false")]; cp_guard = eatom "true"; cp_rhs = f };
              ] }

let inject conf fn kvs extra =
  let pairs =
    (mho_f, fn)
    :: List.concat (List.mapi (fun i (k, v) -> [(mho_k i, k); (mho_v i, v)]) kvs)
    @ extra
  in
  extend_env conf.env pairs

let go conf rest expr env' =
  Running [{ conf with env = env'; cek = { ecxt = rest; term = T_Expr expr } }]

(* maps:fold(Fun, Acc0, Map) — left fold *)
let ho_fold conf rest fn acc kvs =
  let n    = List.length kvs in
  let env' = inject conf fn kvs [(mho_a 0, acc)] in
  let expr =
    List.fold_right
      (fun i inner -> elet (mho_a (i+1)) (eapply mho_f [mho_k i; mho_v i; mho_a i]) inner)
      (List.init n Fun.id)
      (evar (mho_a n))
  in
  go conf rest expr env'

(* maps:map(Fun, Map) — replace each value with Fun(Key, Value) *)
let ho_map conf rest fn kvs =
  let n    = List.length kvs in
  let env' = inject conf fn kvs [] in
  let final = emap_upserts (List.init n (fun i -> (mho_k i, mho_nv i))) in
  let expr =
    List.fold_right
      (fun i inner -> elet (mho_nv i) (eapply mho_f [mho_k i; mho_v i]) inner)
      (List.init n Fun.id)
      final
  in
  go conf rest expr env'

(* maps:filter(Fun, Map) — keep pairs where Fun(Key, Value) = true *)
let ho_filter conf rest fn kvs =
  let n    = List.length kvs in
  let env' = inject conf fn kvs [(mho_a 0, V_map [])] in
  let expr =
    List.fold_right
      (fun i inner ->
        elet (mho_r i) (eapply mho_f [mho_k i; mho_v i])
          (elet (mho_a (i+1))
            (ecase_bool (evar (mho_r i))
              (emap_upserts ~base:(Some (evar (mho_a i))) [(mho_k i, mho_v i)])
              (evar (mho_a i)))
            inner))
      (List.init n Fun.id)
      (evar (mho_a n))
  in
  go conf rest expr env'

(* maps:filtermap(Fun, Map) — Fun returns false or {true, NewValue} *)
let ho_filtermap conf rest fn kvs =
  let n    = List.length kvs in
  let env' = inject conf fn kvs [(mho_a 0, V_map [])] in
  let make_case i =
    Expr_case { case_exp = evar (mho_r i);
                case_pat = [
                  { cp_lhs  = [Pat_tuple [Pat_lit (Lit_atom "true"); Pat_var_name (mho_nv i)]];
                    cp_guard = eatom "true";
                    cp_rhs   = emap_upserts ~base:(Some (evar (mho_a i))) [(mho_k i, mho_nv i)] };
                  { cp_lhs  = [Pat_lit (Lit_atom "false")];
                    cp_guard = eatom "true";
                    cp_rhs   = evar (mho_a i) };
                ] }
  in
  let expr =
    List.fold_right
      (fun i inner ->
        elet (mho_r i) (eapply mho_f [mho_k i; mho_v i])
          (elet (mho_a (i+1)) (make_case i) inner))
      (List.init n Fun.id)
      (evar (mho_a n))
  in
  go conf rest expr env'

(* maps:foreach(Fun, Map) — call Fun(Key, Value) for side effects, return ok *)
let ho_foreach conf rest fn kvs =
  let env'  = inject conf fn kvs [] in
  let calls = List.mapi (fun i _ -> eapply mho_f [mho_k i; mho_v i]) kvs in
  let expr  = Expr_do (calls @ [eatom "ok"]) in
  go conf rest expr env'

(* -------------------------------------------------------------------- *)
(* Dispatch                                                              *)
(* -------------------------------------------------------------------- *)

let dispatch (fun_name : string) (args : value list)
    (conf : process_conf) (rest : eval_cxt)
    : process_conf status =
  let badmap m = raise_exn conf rest Error (V_tuple [V_atom "badmap"; m]) in
  let badarg   = raise_exn conf rest Error (V_atom "badarg") in
  match fun_name, args with

  (* --- Creation -------------------------------------------------------- *)
  | "new", [] ->
     return_val conf rest (V_map [])

  (* --- Lookup ---------------------------------------------------------- *)
  | "get", [k; V_map kvs] ->
     begin match map_lookup k kvs with
     | Some v -> return_val conf rest v
     | None   -> raise_exn conf rest Error (V_tuple [V_atom "badkey"; k])
     end
  | "get", [_; m] -> badmap m

  | "get", [k; V_map kvs; default] ->
     return_val conf rest (match map_lookup k kvs with Some v -> v | None -> default)
  | "get", [_; m; _] -> badmap m

  | "find", [k; V_map kvs] ->
     begin match map_lookup k kvs with
     | Some v -> return_val conf rest (V_tuple [V_atom "ok"; v])
     | None   -> return_val conf rest (V_atom "error")
     end
  | "find", [_; m] -> badmap m

  | "is_key", [k; V_map kvs] ->
     let found = List.exists (fun (k2, _) -> erlang_exact_eq k2 k) kvs in
     return_val conf rest (if found then V_atom "true" else V_atom "false")
  | "is_key", [_; m] -> badmap m

  (* --- Mutation -------------------------------------------------------- *)
  | "put", [k; v; V_map kvs] ->
     return_val conf rest (V_map (map_upsert k v kvs))
  | "put", [_; _; m] -> badmap m

  | "update", [k; v; V_map kvs] ->
     if List.exists (fun (k2, _) -> erlang_exact_eq k2 k) kvs
     then return_val conf rest (V_map (map_upsert k v kvs))
     else raise_exn conf rest Error (V_tuple [V_atom "badkey"; k])
  | "update", [_; _; m] -> badmap m

  | "remove", [k; V_map kvs] ->
     return_val conf rest (V_map (map_remove k kvs))
  | "remove", [_; m] -> badmap m

  | "take", [k; V_map kvs] ->
     begin match map_lookup k kvs with
     | None   -> return_val conf rest (V_atom "error")
     | Some v -> return_val conf rest (V_tuple [v; V_map (map_remove k kvs)])
     end
  | "take", [_; m] -> badmap m

  (* --- Aggregates ------------------------------------------------------ *)
  | "keys", [V_map kvs] ->
     return_val conf rest (to_cons_list (List.map fst kvs))
  | "keys", [m] -> badmap m

  | "values", [V_map kvs] ->
     return_val conf rest (to_cons_list (List.map snd kvs))
  | "values", [m] -> badmap m

  | "size", [V_map kvs] ->
     return_val conf rest (V_int (Z.of_int (List.length kvs)))
  | "size", [m] -> badmap m

  | "to_list", [V_map kvs] ->
     let pairs = List.map (fun (k, v) -> V_tuple [k; v]) kvs in
     return_val conf rest (to_cons_list pairs)
  | "to_list", [m] -> badmap m

  | "from_list", [list] ->
     begin match cons_fold (fun acc pair ->
         match pair with
         | V_tuple [k; v] -> map_upsert k v acc
         | _              -> acc (* skip malformed entries, like OTP does *)) [] list
     with
     | Ok kvs  -> return_val conf rest (V_map kvs)
     | Error _ -> badarg
     end

  | "from_keys", [keys; v] ->
     begin match cons_fold (fun acc k -> map_upsert k v acc) [] keys with
     | Ok kvs  -> return_val conf rest (V_map kvs)
     | Error _ -> badarg
     end

  | "merge", [V_map m1; V_map m2] ->
     (* m2 wins on key conflicts *)
     let merged = List.fold_left (fun acc (k, v) -> map_upsert k v acc) m1 m2 in
     return_val conf rest (V_map merged)
  | "merge", [m; V_map _] -> badmap m
  | "merge", [_; m]       -> badmap m

  (* --- Higher-order ---------------------------------------------------- *)
  | "fold",      [fn; acc; V_map kvs] -> ho_fold      conf rest fn acc kvs
  | "map",       [fn; V_map kvs]      -> ho_map       conf rest fn kvs
  | "filter",    [fn; V_map kvs]      -> ho_filter    conf rest fn kvs
  | "filtermap", [fn; V_map kvs]      -> ho_filtermap conf rest fn kvs
  | "foreach",   [fn; V_map kvs]      -> ho_foreach   conf rest fn kvs
  | ("fold" | "map" | "filter" | "foreach" | "filtermap"), args ->
     (match args with
      | [_; m] | [_; _; m] when (match m with V_map _ -> false | _ -> true) ->
         badmap m
      | _ -> raise_exn conf rest Error (V_atom "badarg"))

  | name, argv ->
     failwith (Printf.sprintf "[maps_bifs] not implemented: maps:'%s'/%d"
       name (List.length argv))
