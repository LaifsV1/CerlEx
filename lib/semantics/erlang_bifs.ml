(** Built-in functions for the [erlang] module.

    Pure (tier-1) operations return a new value and never read [process_conf].
    Process-local (tier-2) operations read but do not modify the concurrent
    network; only [self] falls here currently.
    Global (tier-3) operations such as [!] and [spawn] emit [SR_Send] and
    [SR_Spawn] respectively; the scheduler resolves them.  [spawn/3]
    is [failwith] [WIP] pending module-table threading into BIF dispatch.

    @author Yu-Yang Lin
    @since 2026-05-11
 *)

open Ast
open Term_order

let verbose : bool ref = ref true

(* -------------------------------------------------------------------- *)
(* Helpers                                                               *)
(* -------------------------------------------------------------------- *)

let bool_val b = if b then V_atom "true" else V_atom "false"

let rec is_proper_list = function
  | V_nil -> true
  | V_cons (_, t) -> is_proper_list t
  | _ -> false

let list_append v1 v2 =
  let rec collect acc = function
    | V_nil        -> List.fold_left (fun t h -> V_cons (h, t)) v2 acc
    | V_cons (h,t) -> collect (h :: acc) t
    | _            -> failwith "[erlang_bifs] ++: not a list"
  in
  collect [] v1

let rec list_length acc = function
  | V_nil        -> Z.of_int acc
  | V_cons (_,t) -> list_length (acc + 1) t
  | _            -> failwith "[erlang_bifs] length: not a proper list"

let list_subtract v1 v2 =
  let remove_first x lst =
    let rec go acc = function
      | V_nil -> List.fold_left (fun t h -> V_cons (h, t)) V_nil acc
      | V_cons (h, t) ->
          if erlang_exact_eq h x then
            List.fold_left (fun t h -> V_cons (h, t)) t acc
          else go (h :: acc) t
      | v -> List.fold_left (fun t h -> V_cons (h, t)) v acc
    in
    go [] lst
  in
  let rec collect acc = function
    | V_nil -> acc
    | V_cons (h, t) -> collect (remove_first h acc) t
    | _ -> failwith "[erlang_bifs] --: not a list"
  in
  collect v1 v2

(* -------------------------------------------------------------------- *)
(* Dispatch                                                              *)
(* -------------------------------------------------------------------- *)

let dispatch
    (lookup : string -> string -> int -> closure option)
    (* lookup mod fun arity: resolves a user-defined function for spawn/3;
       passed in from call_dispatch to avoid a circular module dependency *)
    (fun_name : string) (args : value list)
    (conf : process_conf) (rest : eval_cxt)
    : process_conf status =
  match fun_name, args with

  (* --- Arithmetic ---------------------------------------------------
     Erlang's arithmetic operators are dynamically typed: integer op integer
     gives integer; any float operand promotes the result to float.
     Passing a non-numeric argument raises badarith at runtime.          *)

  (* Unary + (identity) and unary - (negation) *)
  | "+",   [V_int n]   -> return_val conf rest (V_int n)
  | "+",   [V_float f] -> return_val conf rest (V_float f)
  | "-",   [V_int n]   -> return_val conf rest (V_int (Z.neg n))
  | "-",   [V_float f] -> return_val conf rest (V_float (-.f))

  (* Binary arithmetic: int * int -> int; any float -> float *)
  | "+",   [V_int a;   V_int b]   -> return_val conf rest (V_int (Z.add a b))
  | "+",   [V_float a; V_float b] -> return_val conf rest (V_float (a +. b))
  | "+",   [V_int a;   V_float b] -> return_val conf rest (V_float (Z.to_float a +. b))
  | "+",   [V_float a; V_int b]   -> return_val conf rest (V_float (a +. Z.to_float b))

  | "-",   [V_int a;   V_int b]   -> return_val conf rest (V_int (Z.sub a b))
  | "-",   [V_float a; V_float b] -> return_val conf rest (V_float (a -. b))
  | "-",   [V_int a;   V_float b] -> return_val conf rest (V_float (Z.to_float a -. b))
  | "-",   [V_float a; V_int b]   -> return_val conf rest (V_float (a -. Z.to_float b))

  | "*",   [V_int a;   V_int b]   -> return_val conf rest (V_int (Z.mul a b))
  | "*",   [V_float a; V_float b] -> return_val conf rest (V_float (a *. b))
  | "*",   [V_int a;   V_float b] -> return_val conf rest (V_float (Z.to_float a *. b))
  | "*",   [V_float a; V_int b]   -> return_val conf rest (V_float (a *. Z.to_float b))

  (* Integer-only operations; non-integer or division by zero -> badarith *)
  | "div", [V_int _; V_int b] when Z.equal b Z.zero -> raise_exn conf rest Error (V_atom "badarith")
  | "div", [V_int a; V_int b]  -> return_val conf rest (V_int (Z.div a b))
  | "rem", [V_int _; V_int b] when Z.equal b Z.zero -> raise_exn conf rest Error (V_atom "badarith")
  | "rem", [V_int a; V_int b]  -> return_val conf rest (V_int (Z.rem a b))

  | "abs",   [V_int n]   -> return_val conf rest (V_int (Z.abs n))
  | "abs",   [V_float f] -> return_val conf rest (V_float (Float.abs f))
  | "round", [V_int n]   -> return_val conf rest (V_int n)
  | "round", [V_float f] -> return_val conf rest (V_int (Z.of_float (Float.round f)))
  | "trunc", [V_int n]   -> return_val conf rest (V_int n)
  | "trunc", [V_float f] -> return_val conf rest (V_int (Z.of_float (Float.of_int (truncate f))))
  | "floor", [V_int n]   -> return_val conf rest (V_int n)
  | "floor", [V_float f] -> return_val conf rest (V_int (Z.of_float (floor f)))
  | "ceil",  [V_int n]   -> return_val conf rest (V_int n)
  | "ceil",  [V_float f] -> return_val conf rest (V_int (Z.of_float (ceil f)))

  (* Wrong type for arithmetic operator *)
  | ("+"|"-"|"*"|"div"|"rem"|"abs"|"round"|"trunc"|"floor"|"ceil"), _ ->
     raise_exn conf rest Error (V_atom "badarith")

  (* --- Comparison --------------------------------------------------- *)
  | "<",   [v1; v2] -> return_val conf rest (bool_val (erlang_compare v1 v2 < 0))
  | ">",   [v1; v2] -> return_val conf rest (bool_val (erlang_compare v1 v2 > 0))
  | "=<",  [v1; v2] -> return_val conf rest (bool_val (erlang_compare v1 v2 <= 0))
  | ">=",  [v1; v2] -> return_val conf rest (bool_val (erlang_compare v1 v2 >= 0))
  | "=:=", [v1; v2] -> return_val conf rest (bool_val (erlang_exact_eq v1 v2))
  | "=/=", [v1; v2] -> return_val conf rest (bool_val (not (erlang_exact_eq v1 v2)))
  | "==",  [v1; v2] -> return_val conf rest (bool_val (erlang_num_eq v1 v2))
  | "/=",  [v1; v2] -> return_val conf rest (bool_val (not (erlang_num_eq v1 v2)))

  (* --- Boolean ------------------------------------------------------ *)
  (* NOTE: passing non-boolean atoms should raise badarg in real Erlang.
     Stricter checking is deferred until needed.                         *)
  | "and", [V_atom "true";  V_atom "true"]  -> return_val conf rest (V_atom "true")
  | "and", [V_atom _;       V_atom _]       -> return_val conf rest (V_atom "false")
  | "or",  [V_atom "false"; V_atom "false"] -> return_val conf rest (V_atom "false")
  | "or",  [V_atom _;       V_atom _]       -> return_val conf rest (V_atom "true")
  | "not", [V_atom "true"]                  -> return_val conf rest (V_atom "false")
  | "not", [V_atom "false"]                 -> return_val conf rest (V_atom "true")
  | "xor", [V_atom "true";  V_atom "false"] -> return_val conf rest (V_atom "true")
  | "xor", [V_atom "false"; V_atom "true"]  -> return_val conf rest (V_atom "true")
  | "xor", [V_atom _;       V_atom _]       -> return_val conf rest (V_atom "false")

  (* --- Type tests --------------------------------------------------- *)
  | "is_atom",     [v] -> return_val conf rest (bool_val (match v with V_atom _    -> true | _ -> false))
  | "is_integer",  [v] -> return_val conf rest (bool_val (match v with V_int _     -> true | _ -> false))
  | "is_float",    [v] -> return_val conf rest (bool_val (match v with V_float _   -> true | _ -> false))
  | "is_number",   [v] -> return_val conf rest
       (bool_val (match v with V_int _ | V_float _ -> true | _ -> false))
  | "is_list",     [v] -> return_val conf rest (bool_val (is_proper_list v))
  | "is_tuple",    [v] -> return_val conf rest (bool_val (match v with V_tuple _   -> true | _ -> false))
  | "is_binary",     [v] -> return_val conf rest
       (bool_val (match v with V_binary (_, len) -> len mod 8 = 0 | _ -> false))
  | "is_bitstring", [v] -> return_val conf rest (bool_val (match v with V_binary _ -> true | _ -> false))
  | "bit_size",  [V_binary (_, len)] -> return_val conf rest (V_int (Z.of_int len))
  | "byte_size", [V_binary (_, len)] ->
      if len mod 8 <> 0 then raise_exn conf rest Error (V_atom "badarg")
      else return_val conf rest (V_int (Z.of_int (len / 8)))
  | "binary_to_list", [V_binary (bits, len)] ->
      if len mod 8 <> 0 then raise_exn conf rest Error (V_atom "badarg")
      else
        let n_bytes = len / 8 in
        let rec loop i acc =
          if i < 0 then acc
          else
            let byte = Z.to_int (Z.logand (Z.shift_right bits (i * 8)) (Z.of_int 0xFF)) in
            loop (i - 1) (V_cons (V_int (Z.of_int byte), acc))
        in
        return_val conf rest (loop (n_bytes - 1) V_nil)
  | "is_pid",      [v] -> return_val conf rest (bool_val (match v with V_pid _     -> true | _ -> false))
  | "is_function", [v] -> return_val conf rest (bool_val (match v with V_closure _ -> true | _ -> false))
  | "is_function", [v; arity] ->
      let result = match v, arity with
        | V_closure clo, V_int n -> List.length clo.clo_vars = Z.to_int n
        | _ -> false
      in
      return_val conf rest (bool_val result)
  | "is_boolean",  [v] -> return_val conf rest
       (bool_val (match v with V_atom "true" | V_atom "false" -> true | _ -> false))
  | "is_map",      [V_map _] -> return_val conf rest (V_atom "true")
  | "is_map",      [_]      -> return_val conf rest (V_atom "false")
  | "is_map_key",  [k; V_map kvs] ->
     return_val conf rest
       (bool_val (List.exists (fun (k2, _) -> erlang_exact_eq k2 k) kvs))
  | "is_map_key",  [_; _] -> raise_exn conf rest Error (V_atom "badmap")
  | "is_record", [V_tuple (V_atom tag :: _ as vs); V_atom expected_tag; V_int size] ->
     return_val conf rest (bool_val (tag = expected_tag && List.length vs = Z.to_int size))
  | "is_record", [_; _; _] -> return_val conf rest (V_atom "false")

  (* --- Tuple operations --------------------------------------------- *)
  | "tuple_to_list", [V_tuple vs] ->
      let lst = List.fold_left (fun acc v -> V_cons (v, acc)) V_nil (List.rev vs) in
      return_val conf rest lst
  | "tuple_to_list", _ -> raise_exn conf rest Error (V_atom "badarg")
  | "list_to_tuple", [v] ->
      let rec to_list acc = function
        | V_nil -> return_val conf rest (V_tuple (List.rev acc))
        | V_cons (h, t) -> to_list (h :: acc) t
        | _ -> raise_exn conf rest Error (V_atom "badarg")
      in
      to_list [] v
  | "list_to_tuple", _ -> raise_exn conf rest Error (V_atom "badarg")
  | "tuple_size", [V_tuple vs] ->
      return_val conf rest (V_int (Z.of_int (List.length vs)))
  | "tuple_size", _ -> raise_exn conf rest Error (V_atom "badarg")
  | "element", [V_int n; V_tuple vs] ->
      let i = Z.to_int n in
      let len = List.length vs in
      if i < 1 || i > len then raise_exn conf rest Error (V_atom "badarg")
      else return_val conf rest (List.nth vs (i - 1))
  | "element", _ -> raise_exn conf rest Error (V_atom "badarg")
  | "setelement", [V_int n; V_tuple vs; v] ->
      let i = Z.to_int n in
      let len = List.length vs in
      if i < 1 || i > len then raise_exn conf rest Error (V_atom "badarg")
      else
        let vs' = List.mapi (fun j x -> if j = i - 1 then v else x) vs in
        return_val conf rest (V_tuple vs')
  | "setelement", _ -> raise_exn conf rest Error (V_atom "badarg")

  (* --- List operations ---------------------------------------------- *)
  | "++",      [v1; v2] -> return_val conf rest (list_append v1 v2)
  | "--",      [v1; v2] -> return_val conf rest (list_subtract v1 v2)
  | "length",  [v]      -> return_val conf rest (V_int (list_length 0 v))

  (* --- Process-local (tier 2) --------------------------------------- *)
  | "self", [] -> return_val conf rest (V_pid conf.pid)

  (* --- Debug output --------------------------------------------------
     erlang:display/1 is BEAM's low-level debug print: it bypasses the io
     system entirely (no io-server message, so it is not a scheduling event
     -- which is why Concuerror's test programs use it instead of
     io:format).  Prints the term and returns 'true'.  Gated on -no-io:
     the flag's purpose is suppressing program output during exploration,
     so it covers display too, even though BEAM's display bypasses io. *)
  | "display", [v] ->
     if not !Io_bifs.suppress_io then
       Format.printf "%a@." Value_printer.pp v;
     return_val conf rest (V_atom "true")

  (* --- Global effects: suspend with stuck_reason (tier 3) ----------- *)
  | "!", [V_pid dst; msg] ->
     Stuck (SR_Send { dst; msg }, { conf with cek = { ecxt = rest; term = T_Vals [msg] } })
  | "!", _ ->
     raise_exn conf rest Error (V_atom "badarg")
  | "spawn", [V_closure clo] ->
     Stuck (SR_Spawn { clo; args = []; cont = rest }, conf)
  | "spawn", [V_atom mod_name; V_atom fun_name; arg_list] ->
     let rec values_of_list acc = function
       | V_nil -> List.rev acc
       | V_cons (h, t) -> values_of_list (h :: acc) t
       | _ -> failwith "[erlang_bifs] spawn/3: args must be a proper list"
     in
     let args = values_of_list [] arg_list in
     let arity = List.length args in
     begin match lookup mod_name fun_name arity with
     | None ->
        failwith (Printf.sprintf "[erlang_bifs] spawn/3: undefined '%s':'%s'/%d"
                    mod_name fun_name arity)
     | Some clo ->
        Stuck (SR_Spawn { clo; args; cont = rest }, conf)
     end

  (* --- Hash ---------------------------------------------------------- *)
  | "phash",  [v; V_int range] | "phash2", [v; V_int range] ->
      (match v with
       | V_closure _ when !verbose ->
           Format.eprintf "[erlang_bifs] warning: phash on closure -- hash is structural, not identity-based@."
       | _ -> ());
      let b = Marshal.to_bytes v [Marshal.Closures] in
      let h = Hashtbl.hash b in
      let r = Z.to_int range in
      return_val conf rest (V_int (Z.of_int (h mod r + 1)))
  | "phash2", [v] ->
      (match v with
       | V_closure _ when !verbose ->
           Format.eprintf "[erlang_bifs] warning: phash2 on closure -- hash is structural, not identity-based@."
       | _ -> ());
      let b = Marshal.to_bytes v [Marshal.Closures] in
      let h = Hashtbl.hash b in
      return_val conf rest (V_int (Z.of_int (h mod 134217728)))
  | "phash", _  | "phash2", _ -> raise_exn conf rest Error (V_atom "badarg")

  (* --- Exception raisers -------------------------------------------- *)
  | "error", [reason]       -> raise_exn conf rest Error reason
  | "error", [reason; _stk] -> raise_exn conf rest Error reason
  | "throw", [reason]       -> raise_exn conf rest Throw reason
  | "exit",  [reason]       -> raise_exn conf rest Exit  reason

  (* --- Process dictionary -------------------------------------------- *)
  | "put", [k; v] ->
     let old = match List.assoc_opt k conf.pdict with
       | Some ov -> ov
       | None    -> V_atom "undefined"
     in
     let pdict' = (k, v) :: List.filter (fun (k2, _) -> k2 <> k) conf.pdict in
     return_val { conf with pdict = pdict' } rest old
  | "erase", [k] ->
     let old = match List.assoc_opt k conf.pdict with
       | Some ov -> ov
       | None    -> V_atom "undefined"
     in
     return_val { conf with pdict = List.filter (fun (k2, _) -> k2 <> k) conf.pdict } rest old
  | "get", [k] ->
     let v = match List.assoc_opt k conf.pdict with
       | Some ov -> ov
       | None    -> V_atom "undefined"
     in
     return_val conf rest v
  | "get", [] ->
     let list = List.fold_right
       (fun (k, v) acc -> V_cons (V_tuple [k; v], acc))
       conf.pdict V_nil
     in
     return_val conf rest list
  | "erase", [] ->
     let list = List.fold_right
       (fun (k, v) acc -> V_cons (V_tuple [k; v], acc))
       conf.pdict V_nil
     in
     return_val { conf with pdict = [] } rest list

  (* --- Map guard BIFs ------------------------------------------------ *)
  | "map_get", [k; V_map kvs] ->
     begin match List.find_opt (fun (k2, _) -> erlang_exact_eq k2 k) kvs with
     | Some (_, v) -> return_val conf rest v
     | None        -> raise_exn conf rest Error (V_tuple [V_atom "badkey"; k])
     end
  | "map_get", [_; _] -> raise_exn conf rest Error (V_atom "badmap")
  | "map_size", [V_map kvs] ->
     return_val conf rest (V_int (Z.of_int (List.length kvs)))
  | "map_size", [_] -> raise_exn conf rest Error (V_atom "badmap")

  (* --- Module introspection (stub) ----------------------------------- *)
  | "get_module_info", [_m]     -> return_val conf rest V_nil
  | "get_module_info", [_m; _k] -> return_val conf rest V_nil

  (* --- Refs (type test only; make_ref/0 and comparison branching in dispatch_r) --- *)
  | "is_reference", [v] -> return_val conf rest (bool_val (match v with V_ref _ | V_ets_tid _ -> true | _ -> false))

  (* --- Unknown ------------------------------------------------------- *)
  | name, argv ->
     failwith (Printf.sprintf "[erlang_bifs] not implemented: erlang:'%s'/%d"
                 name (List.length argv))

(* -------------------------------------------------------------------- *)
(* Refs-aware dispatch                                                   *)
(* -------------------------------------------------------------------- *)

(** Handles BIFs that need access to [ref_env]:
    - [make_ref/0]: allocates a fresh symbolic ref.
    - Ordering comparisons ([<] [>] [=<] [>=]) on two distinct [V_ref]s:
      branches on both orderings, pruning cycles via [Ref_order.add_constraint].
    All other calls fall through to [dispatch] with [lift_refs refs].
    Equality/inequality ([=:=] [=/=] [==] [/=]) on refs compare IDs
    deterministically and need no special handling. *)
let dispatch_r
    (lookup : string -> string -> int -> closure option)
    (refs : ref_env)
    (fun_name : string) (args : value list)
    (conf : process_conf) (rest : eval_cxt)
    : (ref_env * process_conf) status =
  match fun_name, args with

  | "make_ref", [] ->
     (* make_ref is a clock event: bump the creator's own component and stamp
        the ref with (creator, post-bump clock).  This makes each creation a
        distinct event so creation_order can tell causally-ordered creations
        apart from concurrent ones.  See notes/ref_creation_order_plan.md. *)
     let id     = refs.next_id in
     let clock' = clock_bump conf.pid conf.clock in
     let refs'  = { refs with next_id = id + 1
                            ; stamps  = (id, (conf.pid, clock')) :: refs.stamps } in
     Running [(refs', { conf with clock = clock'
                                ; cek = { ecxt = rest; term = T_Vals [V_ref id] } })]

  (* Same-kind pairs (ref/ref, tid/tid) are creation-ordered on BEAM and stay
     symbolic; both kinds share the id space and stamp discipline, so one arm
     serves both. *)
  | ("<" | ">" | "=<" | ">="),
    ([V_ref a; V_ref b] | [V_ets_tid a; V_ets_tid b]) when a <> b ->
     let branch lt order_opt =
       match order_opt with
       | None -> None
       | Some order' ->
         let result = match fun_name with
           | "<" | "=<" -> lt
           | _          -> not lt   (* ">" | ">=" *)
         in
         Some ({ refs with order = order' },
               { conf with cek = { ecxt = rest; term = T_Vals [bool_val result] } })
     in
     (* Consult creation order first.  If one creation causally precedes the
        other, the ordering is forced -- emit a single branch (still through
        add_constraint, so the forced edge enters [order] and composes with any
        edges chosen for concurrent pairs under cycle detection).  Only
        genuinely concurrent creations branch both ways. *)
     begin match creation_order refs a b with
       | Some true ->
          Running (List.filter_map Fun.id [ branch true (Ref_order.add_constraint refs.order a b) ])
       | Some false ->
          Running (List.filter_map Fun.id [ branch false (Ref_order.add_constraint refs.order b a) ])
       | None ->
          Running (List.filter_map Fun.id
            [ branch true  (Ref_order.add_constraint refs.order a b)
            ; branch false (Ref_order.add_constraint refs.order b a) ])
     end

  (* Mixed-kind ordering (make_ref ref vs ETS tid) is NOT creation-ordered on
     BEAM: tids are magic refs and cross-kind order is implementation-defined
     (measured 2026-07-07: ordinary refs < tids regardless of creation order;
     caught by Concuerror failing a creation-order assertion).  Modelling it
     as creation-forced gives wrong deterministic answers, so it kills the
     whole exploration as unsupported. *)
  | ("<" | ">" | "=<" | ">="),
    ([V_ref _; V_ets_tid _] | [V_ets_tid _; V_ref _]) ->
     failwith "[ets] unsupported in v0: ordering a make_ref reference against \
               an ETS tid (cross-kind ref order is implementation-defined on \
               BEAM; see notes/ets_plan.md)"

  | _ -> lift_refs refs (dispatch lookup fun_name args conf rest)
