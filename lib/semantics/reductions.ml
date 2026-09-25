(** Small-step reductions for Core Erlang process configurations.

    This module implements CEK focusing and one-step process-local reduction.
    It assumes compiler-normalised Core Erlang: source-level strings and
    proper-list syntax should not reach the reducer.

    [Stuck] is reserved for configurations that need an environment/opponent
    action, not for malformed terms or runtime errors.

    @author Yu-Yang Lin
    @since 2026-04-17
 *)

open Syntax.Core_ast
open Ast

(******************)
(* FOCUS FUNCTION *)
(******************)

(** Focus one step into the next reducible subexpression, pushing the
    corresponding CEK frame. Returns [None] when already at a redex/result.
    Assumes compiler-normalised Core; unexpected strings/proper lists are errors.
 *)
let focus (c : process_conf) : process_conf option =
  let focus_error msg = failwith ("[focus] " ^ msg) in
  let rho = c.env in
  let push fr e = Some {c with cek = {ecxt = fr :: c.cek.ecxt; term = T_Expr e}} in
  match c.cek.term with
  | T_Vals _ | T_Raise _ -> None    (* can't focus results or exceptions *)
  | T_Expr e ->
     begin
       match e with
       | Expr_literal (Lit_string _) ->                                   (* reject non-normalised Core *)
          focus_error "unexpected string literal; expected compiler-normalised Core"
       | Expr_list [] ->                                                  (* normalize proper-list syntax *)
          Some { c with cek = { c.cek with term = T_Expr (Expr_literal Lit_nil) } }
       | Expr_list (e1 :: es) ->
          push (E_ConsHd ([], es, Expr_literal Lit_nil, rho)) e1
       | Expr_var _ | Expr_literal _ | Expr_fname _ | Expr_fun _ -> None  (* can't focus atomic expressions *)
       | Expr_val_list [] -> None                                         (* value sequences *)
       | Expr_val_list (e1 :: es) -> push (E_ValList ([], es, rho)) e1
       | Expr_tuple [] -> None                                            (* tuples *)
       | Expr_tuple (e1 :: es) -> push (E_Tuple ([], es, rho)) e1
       | Expr_cons (e1 :: es, tl) -> push (E_ConsHd ([], es, tl, rho)) e1 (* lists *)
       | Expr_cons ([], _) -> focus_error "malformed cons expression with no head"
       | Expr_binary [] -> None                                           (* bitstrings *)
       | Expr_binary ({ bits_lhs; bits_rhs } :: segs) -> push (E_BitstrLhs ((Z.zero, 0), bits_rhs, segs, rho)) bits_lhs
       | Expr_let { lb_lhs; lb_expr; lb_rhs } -> push (E_Let (lb_lhs, lb_rhs, rho)) lb_expr
       | Expr_letrec _ -> None      (* makes more sense to implement as a reduction instead of by focussing *)
       | Expr_case { case_exp; case_pat } -> push (E_Case (case_pat, rho)) case_exp
       | Expr_apply { fn_name; fn_args } -> push (E_ApplyFun (fn_args, rho)) fn_name
       | Expr_qualified_call { qc_mod; qc_fun; qc_args } -> push (E_QCallMod (qc_fun, qc_args, rho)) qc_mod
       | Expr_primop { pop_name; pop_args } ->
          begin
            match pop_args with
            | [] -> None
            | e1 :: es -> push (E_PrimOp (pop_name, [], es, rho)) e1
          end
       | Expr_try { tc_exp; tc_vars; tc_in; tc_catch_vars; tc_catch } ->
          push (E_Try (tc_vars, tc_in, tc_catch_vars, tc_catch, rho)) tc_exp
       | Expr_receive { rcv_pat; tm_after; tm_body } -> push (E_Receive (rcv_pat, tm_body, rho)) tm_after
       | Expr_do [] -> None
       | Expr_do (e1 :: es) -> push (E_Do (es, rho)) e1
       | Expr_catch e1 -> push E_Catch e1
       | Expr_map { map_base; map_assocs = [] } ->
          begin match map_base with
          | None        -> Some { c with cek = { c.cek with term = T_Vals [V_map []] } }
          | Some base_e -> push (E_MapBase ([], rho)) base_e
          end
       | Expr_map { map_base; map_assocs = first :: rest_as } ->
          push (E_MapKey ([], first.ma_op, first.ma_val, rest_as, map_base, rho)) first.ma_key
     end

(********************************)
(* START OF REDUCTION FUNCTIONS *)
(********************************)

(** function to terminate current execution if a problem is encountered while reducing *)
let reduction_error (c : process_conf) msg =
  Format.eprintf "[reductions] %s@." msg;
  Format.eprintf "Last CEK term:@.%s@."
    (Sexplib0.Sexp.to_string_hum (sexp_of_cek_term c.cek));
  failwith ("[reductions] " ^ msg)

(*****************************************)
(* BLOCK OF ENVIRONMENT HELPER FUNCTIONS *)
(*****************************************)

(** empty environment rho; has two empty maps *)
let empty_env : env = { vars = VarMap.empty; funs = FnameMap.empty }

(** function to bind one var to one value in rho*)
let bind_var x v rho = { rho with vars = VarMap.add x v rho.vars }

(** function to bind a list of variables to a list of values of the same length *)
let bind_vars c xs vs rho =
  let rec aux acc xs vs =
    match xs, vs with
    | [], [] -> acc
    | x :: xs, v :: vs -> aux (bind_var x v acc) xs vs
    | _ -> reduction_error c "degree mismatch while binding variables"
  in
  aux rho xs vs

(** function to extend the current variable bindings in a rho with a given vars bindings *)
let extend_vars vars rho = { rho with vars = VarMap.fold (fun x v acc -> VarMap.add x v acc) vars rho.vars }

(*********************************************)
(* BLOCK OF VALUE BUILLDING HELPER FUNCTIONS *)
(*********************************************)

(** function to convert a literal to a value *)
let rec literal_to_value = function
  | Lit_string _ -> failwith "[internal error] unexpected string in [literal_to_value]; should have been caught earlier"
  | Lit_list lits ->
     List.fold_right (fun l acc -> V_cons (literal_to_value l, acc)) lits V_nil
  | Lit_integer n -> V_int (Z.of_int n)
  | Lit_float f -> V_float f
  | Lit_char c -> V_char c
  | Lit_atom a -> V_atom a
  | Lit_nil -> V_nil
  | Lit_cons (xs, tl) ->
     List.fold_right
       (fun x acc -> V_cons (literal_to_value x, acc))
       xs
       (literal_to_value tl)
  | Lit_tuple xs -> V_tuple (List.map literal_to_value xs)
  | Lit_map kvs  ->
      let pairs = List.map (fun (k, v) -> (literal_to_value k, literal_to_value v)) kvs in
      V_map (List.sort_uniq (fun (k1,_) (k2,_) -> Term_order.erlang_compare k1 k2) pairs)

(** Fold a reversed head-value list onto a tail value to produce a cons chain.
    [mk_cons [vn;...;v1] tail] = [v1,...,vn | tail]. *)
let mk_cons heads_rev tail =
  List.fold_left (fun acc hd -> V_cons (hd, acc)) tail heads_rev

(* Insert or replace a key-value pair in a sorted map list, maintaining
   ascending Erlang term order by key. *)
let map_upsert k v kvs =
  let kvs' = List.filter (fun (k2, _) -> not (Term_order.erlang_exact_eq k2 k)) kvs in
  let rec insert = function
    | [] -> [(k, v)]
    | ((k2, _) as pair) :: rest ->
        if Term_order.erlang_compare k k2 <= 0 then (k, v) :: pair :: rest
        else pair :: insert rest
  in
  insert kvs'

(* Apply one map assoc (upsert or exact-update) to a sorted map list. *)
let apply_assoc_to (c : process_conf) (kvs : (value * value) list)
    ((op, k, v) : map_assoc_op * value * value) : (value * value) list =
  match op with
  | MapAssoc -> map_upsert k v kvs
  | MapExact ->
      if List.exists (fun (k2, _) -> Term_order.erlang_exact_eq k2 k) kvs
      then List.map (fun (k2, v2) -> if Term_order.erlang_exact_eq k2 k then (k2, v) else (k2, v2)) kvs
      else reduction_error c "map exact update: key not present in map"

(** Evaluate one bitstring segment parameter expression in a given environment.
    Handles literals, variable references, and cons/list constructions (which
    appear in the flags parameter, e.g. ['unsigned'|['big']]).  Used by
    [decode_bitstring_segments] to resolve size variables bound earlier in
    the same pattern. *)
let rec eval_bitstr_param (c : process_conf) (rho : env) (e : expr) : value =
  match e with
  | Expr_literal lit -> literal_to_value lit
  | Expr_var x ->
      (match VarMap.find_opt x rho.vars with
       | Some v -> v
       | None -> reduction_error c ("bitstring: unbound variable in segment parameter: " ^ x))
  | Expr_list [] -> V_nil
  | Expr_list (e1 :: es) ->
      V_cons (eval_bitstr_param c rho e1, eval_bitstr_param c rho (Expr_list es))
  | Expr_cons (heads, tl) ->
      List.fold_right
        (fun h acc -> V_cons (eval_bitstr_param c rho h, acc))
        heads (eval_bitstr_param c rho tl)
  | _ -> reduction_error c "bitstring: unsupported expression in segment parameter position"

(** function to convert an exception class into a Cerl atom.
    NOTE: we assume these are all the classes based on the Erlang documentation:
    --------------
    Class	Origin
    [error]	Run-time error, for example, 1+a, or the process called error/1
    [exit]	The process called exit/1
    [throw]	The process called throw/1
    --------------
    @see <https://www.erlang.org/doc/system/errors.html#exceptions> Erlang errors and exception classes
 *)
let value_of_exception_class = function
  | Error -> V_atom "error"
  | Exit  -> V_atom "exit"
  | Throw -> V_atom "throw"

(***************************************)
(* BLOCK OF EXCEPTION RESULT FUNCTIONS *)
(***************************************)

(** function to create a new value sequence (result) out of an exception.
    NOTE: Core Erlang 1.0.3 describes Erlang implementations as using three
    exception variables, but OTP compiler output can use two-variable catch
    handlers for guard wrappers that only need class/reason.  Reason and info
    stay as values to leave room for implementation-defined exception payloads.
 *)
let exception_values c ex n =
  match n with
  | 2 -> [ value_of_exception_class ex.class_; ex.reason ]
  | 3 -> [ value_of_exception_class ex.class_; ex.reason; ex.info ]
  | _ -> reduction_error c "try/catch expects two or three exception variables"

(** function that implements the result shape of the standalone [catch] expression.
    NOTE: we don't desugar [catch] expressions.

    Erlang exceptions have one of three classes: [error], [exit], or [throw],
    together with a reason and stack trace. [catch] maps these as:
    - [throw] -> Reason
    - [exit]  -> {'EXIT', Reason}
    - [error] -> {'EXIT', {Reason, Stacktrace}}

    Core Erlang specifies this using a desugaring of [catch] into [try],
    where the error case uses [primop exc_trace(Info)].
    
    TODO: OTP compiler output may also use [primop build_stacktrace(Info)].
    Until that primitive is implemented, we use [] as the stacktrace placeholder.

    References:
    - Erlang errors and exception classes:
    https://www.erlang.org/doc/system/errors.html
    - Erlang expressions, including catch/try behavior:
    https://www.erlang.org/doc/system/expressions.html
    - erlang:raise/3 and exception class/reason/stacktrace:
    https://www.erlang.org/doc/apps/erts/erlang.html
    - proc_lib exception type {Class, Reason} | {Class, Reason, Stacktrace}:
    https://www.erlang.org/doc/apps/stdlib/proc_lib.html
    - Core Erlang 1.0.3 specification, Section 6.4 Catch
 *)
let catch_result ex =
  match ex.class_ with
  | Throw -> [ex.reason]
  | Exit  -> [V_tuple [V_atom "EXIT"; ex.reason]]
  | Error ->
     (* TODO: Core Erlang catch uses [primop exc_trace(Info)] /
        compiler Core may use [primop build_stacktrace(Info)].
        There is no primitive/runtime module yet, so this currently
        uses [] as the trace. *)
     [V_tuple [V_atom "EXIT"; V_tuple [ex.reason; V_nil]]]

(******************************************)
(* BLOCK OF PATTERN MATCHING HELPERS      *)
(******************************************)

(** Match one pattern against one value; return [Some bindings] on success,
    [None] on mismatch.

    [Pat_cons (heads, tl_pat)] walks [heads] against successive [V_cons] cells
    and then matches [tl_pat] against the remaining tail.  This handles both
    proper and improper list patterns.

    Bindings from sub-matches are merged with left-bias via [VarMap.union].
    Patterns should not rebind the same variable, so either side is equivalent.
 *)
let rec match_pattern (c : process_conf) (rho : env) (p : pattern) (v : value)
        : value VarMap.t option =
  match p with
  | Pat_lit lit ->
     (* Structural equality; float NaN edge cases are intentionally ignored. *)
     if literal_to_value lit = v then Some VarMap.empty else None
  | Pat_var_name x ->
     Some (VarMap.add x v VarMap.empty)
  | Pat_tuple ps ->
     begin
       match v with
       | V_tuple vs -> match_patterns c rho ps vs
       | _ -> None
     end
  | Pat_list ps ->
     (* Proper-list pattern, the pattern-side analogue of [Expr_list] (OTP 26
        emits it for literal-shaped list patterns, e.g. [{k,V}] = ...).
        Walk elements against successive cons cells; the tail must be nil. *)
     let rec go hs cur =
       match hs with
       | [] -> if cur = V_nil then Some VarMap.empty else None
       | ph :: pt ->
          begin match cur with
          | V_cons (h, t) ->
             begin match match_pattern c rho ph h with
             | None -> None
             | Some b1 ->
                begin match go pt t with
                | None -> None
                | Some b2 -> Some (VarMap.union (fun _ x _ -> Some x) b1 b2)
                end
             end
          | _ -> None
          end
     in
     go ps v
  | Pat_cons (heads, tl_pat) ->
     let rec go hs cur =
       match hs with
       | [] -> match_pattern c rho tl_pat cur
       | ph :: pt ->
          match cur with
          | V_cons (h, t) ->
             begin
               match match_pattern c rho ph h with
               | None -> None
               | Some b1 ->
                  begin
                    match go pt t with
                    | None -> None
                    | Some b2 -> Some (VarMap.union (fun _ a _ -> Some a) b1 b2)
                  end
             end
          | _ -> None
     in
     go heads v
  | Pat_bitstring segs ->
     begin
       match v with
       | V_binary (bits, len) -> decode_bitstring_segments c rho segs (bits, len) VarMap.empty
       | _ -> None
     end
  | Pat_alias (x, p') ->
     begin
       match match_pattern c rho p' v with
       | None -> None
       | Some bs -> Some (VarMap.add x v bs)
     end
  | Pat_map assocs ->
     begin match v with
     | V_map kvs ->
         let eval_key = function
           | Expr_literal lit -> literal_to_value lit
           | Expr_var x ->
               (match VarMap.find_opt x rho.vars with
                | Some kv -> kv
                | None -> reduction_error c ("map pattern: unbound key variable: " ^ x))
           | _ -> reduction_error c "map pattern: unsupported key expression (expected literal or bound variable)"
         in
         List.fold_left (fun acc_opt { mpa_key; mpa_pat } ->
             match acc_opt with
             | None -> None
             | Some bindings ->
                 let key = eval_key mpa_key in
                 begin match List.find_opt (fun (k2, _) -> Term_order.erlang_exact_eq k2 key) kvs with
                 | None         -> None
                 | Some (_, mv) ->
                     begin match match_pattern c rho mpa_pat mv with
                     | None    -> None
                     | Some bs -> Some (VarMap.union (fun _ a _ -> Some a) bindings bs)
                     end
                 end
         ) (Some VarMap.empty) assocs
     | _ -> None
     end

(** Match a list of patterns against a list of values of the same length.
    Returns [None] on any mismatch or length difference. *)
and match_patterns c rho ps vs =
  match ps, vs with
  | [], [] -> Some VarMap.empty
  | p :: ps', v :: vs' ->
     begin
       match match_pattern c rho p v with
       | None -> None
       | Some b1 ->
          match match_patterns c rho ps' vs' with
          | None -> None
          | Some b2 -> Some (VarMap.union (fun _ a _ -> Some a) b1 b2)
     end
  | _ -> None

(** Decode a bitstring against a list of segment patterns, threading bindings
    through so that earlier segments' bound variables are visible in later
    segments' size expressions.  Returns [Some bindings] if all segments match
    and the buffer is exactly consumed, [None] otherwise. *)
and decode_bitstring_segments c rho segs buf acc =
  match segs with
  | [] ->
     if snd buf = 0 then Some acc else None
  | { bits_pat_lhs; bits_pat_rhs } :: rest ->
     let rho_ext = extend_vars acc rho in
     let param_vals = List.map (eval_bitstr_param c rho_ext) bits_pat_rhs in
     begin match Bitstring_params.of_value_list param_vals with
     | Error _ -> None
     | Ok params ->
        begin match Bitstring_codec.decode_segment buf params with
        | None -> None
        | Some (value, buf') ->
           begin match match_pattern c rho_ext bits_pat_lhs value with
           | None -> None
           | Some new_bs ->
               let acc' = VarMap.union (fun _ a _ -> Some a) acc new_bs in
               decode_bitstring_segments c rho rest buf' acc'
           end
        end
     end

(********************************)
(* CLOSURE APPLICATION HELPER   *)
(********************************)

(** Apply a closure to an argument list.

    The body executes in the closure's captured environment extended with the
    formal parameter bindings.  [rest] is the call-site continuation (the
    evaluation context that was in place when the apply frame was popped). *)

let apply_closure (refs : ref_env) (c : process_conf) rest v args
    : (ref_env * process_conf) status =
  match v with
  | V_closure clo ->
     let rho' = bind_vars c clo.clo_vars args clo.clo_env in
     Running [(refs, { c with env = rho'; cek = { ecxt = rest; term = T_Expr clo.clo_body } })]
  | _ -> reduction_error c "apply: not a closure"

(*****************************)
(* MAIN REDUCTION FUNCTION   *)
(*****************************)

(** One-step reduction.  Returns:
    - [Running [c']] : the configuration stepped to [c'].
    - [Done c]       : evaluation is complete ([T_Vals] or [T_Raise] with empty context).
    - [Stuck (reason, c)] : requesting a network/global action such as receive,
      send, or spawn.

    This function should only be called after [focus] has returned [None].
    Every case that [focus] can push a frame for is handled by [focus]; reaching
    [reduce] with such a term is a bug and raises via [reduction_error].
 *)
let rec reduce (mt : Call_dispatch.module_table) (refs : ref_env) (c : process_conf)
    : (ref_env * process_conf) status =
  let running c' = Running [(refs, c')] in
  match c.cek.term, c.cek.ecxt with

  (*------------------------------------------------------------------*)
  (* Terminal states                                                   *)
  (*------------------------------------------------------------------*)

  (* A value sequence or uncaught exception at the top level: done. *)
  | T_Vals _,  [] -> Done (refs, c)
  | T_Raise _, [] -> Done (refs, c)

  (*------------------------------------------------------------------*)
  (* Redex rules : T_Expr e                                           *)
  (*------------------------------------------------------------------*)

  (* Variable lookup: substitute the bound value. *)
  | T_Expr (Expr_var x), ecxt ->
     begin
       match VarMap.find_opt x c.env.vars with
       | Some v -> running { c with cek = { ecxt; term = T_Vals [v] } }
       | None   -> reduction_error c ("unbound variable: " ^ x)
     end

  (* Function-name lookup: retrieve closure from the function environment. *)
  | T_Expr (Expr_fname f), ecxt ->
     begin
       match FnameMap.find_opt f c.env.funs with
       | Some clo -> running { c with cek = { ecxt; term = T_Vals [V_closure clo] } }
       | None     -> reduction_error c ("unbound function name: " ^ f.fn_name)
     end

  (* Literals reduce directly to values. *)
  | T_Expr (Expr_literal lit), ecxt ->
     running { c with cek = { ecxt; term = T_Vals [literal_to_value lit] } }

  (* A fun-expression builds a closure capturing the current environment. *)
  | T_Expr (Expr_fun fe), ecxt ->
     let clo = { clo_vars = fe.fe_vars; clo_body = fe.fe_body; clo_env = c.env } in
     running { c with cek = { ecxt; term = T_Vals [V_closure clo] } }

  (* Empty forms : focus returns None for these, so reduce handles them. *)
  | T_Expr (Expr_val_list []), ecxt ->
     running { c with cek = { ecxt; term = T_Vals [] } }
  | T_Expr (Expr_tuple []), ecxt ->
     running { c with cek = { ecxt; term = T_Vals [V_tuple []] } }
  | T_Expr (Expr_binary []), ecxt ->
     running { c with cek = { ecxt; term = T_Vals [V_binary (Z.zero, 0)] } }
  | T_Expr (Expr_do []), ecxt ->
     (* An empty do-sequence has no value to return; produce an empty sequence. *)
     running { c with cek = { ecxt; term = T_Vals [] } }

  (* Letrec : install the mutually-recursive closure group, then evaluate the body.
     The wrap trick: each closure's body is wrapped in another Expr_letrec over the
     same group.  On every call, the letrec is re-evaluated, re-installing the whole
     group before the original body runs.  This correctly handles mutual recursion
     without needing circular mutable state.  A simpler two-pass build is wrong: after
     two levels of mutual calls the captured env no longer contains the group. *)
  | T_Expr (Expr_letrec { lrb_lhs; lrb_rhs }), ecxt ->
     let funs =
       List.fold_left (fun acc fd ->
           let fe = fd.fd_body in
           let clo = { clo_vars = fe.fe_vars;
                       clo_body = Expr_letrec { lrb_lhs; lrb_rhs = fe.fe_body };
                       clo_env  = c.env } in
           FnameMap.add fd.fd_name clo acc)
         c.env.funs lrb_lhs
     in
     let rho' = { c.env with funs } in
     running { c with env = rho'; cek = { ecxt; term = T_Expr lrb_rhs } }

  (* Nullary primop: focus returns None for these, so reduce handles them. *)
  | T_Expr (Expr_primop { pop_name; pop_args = [] }), ecxt ->
     lift_refs refs (Primops.dispatch pop_name [] c ecxt)

  (* Any other T_Expr that reaches reduce without a prior focus step is a bug. *)
  | T_Expr _, _ ->
     reduction_error c "non-atomic expression reached reduce without focusing"

  (*------------------------------------------------------------------*)
  (* Frame-unwinding rules : T_Vals vs, frame :: rest                 *)
  (*------------------------------------------------------------------*)

  (* --- Value lists ---
     E_ValList accumulates singleton values into a multi-value sequence.
     When the pending list is empty, reverse the accumulator and return.
     When more expressions remain, evaluate the next one. *)
  | T_Vals [v], E_ValList (acc, [], rho) :: rest ->
     running { c with env = rho; cek = { ecxt = rest; term = T_Vals (List.rev (v :: acc)) } }
  | T_Vals [v], E_ValList (acc, e :: es, rho) :: rest ->
     running { c with env = rho; cek = { ecxt = E_ValList (v :: acc, es, rho) :: rest; term = T_Expr e } }
  | T_Vals _, E_ValList _ :: _ ->
     reduction_error c "degree mismatch in value-list element"

  (* --- Tuples ---
     Same accumulate-then-build pattern as value lists. *)
  | T_Vals [v], E_Tuple (acc, [], rho) :: rest ->
     running { c with env = rho; cek = { ecxt = rest; term = T_Vals [V_tuple (List.rev (v :: acc))] } }
  | T_Vals [v], E_Tuple (acc, e :: es, rho) :: rest ->
     running { c with env = rho; cek = { ecxt = E_Tuple (v :: acc, es, rho) :: rest; term = T_Expr e } }
  | T_Vals _, E_Tuple _ :: _ ->
     reduction_error c "degree mismatch in tuple element"

  (* --- Cons cells ---
     E_ConsHd evaluates the head elements left-to-right.  When all heads are
     done, transition to E_ConsTl to evaluate the tail.
     E_ConsTl folds the reversed head-value list onto the tail via [mk_cons]. *)
  | T_Vals [v], E_ConsHd (acc, [], tl, rho) :: rest ->
     running { c with env = rho; cek = { ecxt = E_ConsTl (v :: acc) :: rest; term = T_Expr tl } }
  | T_Vals [v], E_ConsHd (acc, e :: es, tl, rho) :: rest ->
     running { c with env = rho; cek = { ecxt = E_ConsHd (v :: acc, es, tl, rho) :: rest; term = T_Expr e } }
  | T_Vals _, E_ConsHd _ :: _ ->
     reduction_error c "degree mismatch in cons head"

  | T_Vals [tl], E_ConsTl acc :: rest ->
     (* acc is the head list in reverse; mk_cons folds it onto the tail. *)
     running { c with cek = { ecxt = rest; term = T_Vals [mk_cons acc tl] } }
  | T_Vals _, E_ConsTl _ :: _ ->
     reduction_error c "degree mismatch in cons tail"

  (* --- Bitstring segments ---
     E_BitstrLhs has evaluated the segment value (lhs).  If the segment has no
     rhs params, encode immediately.  Otherwise push E_BitstrRhs to evaluate them.
     E_BitstrRhs accumulates the rhs param values.  When all are done, encode the
     segment and call finish_bitstring_segment to move to the next segment or close. *)
  | T_Vals [_lhs], E_BitstrLhs (_acc, [], _segs, _rho) :: _rest ->
     reduction_error c "bitstring segment with no parameters (unexpected in OTP-compiled Core)"
  | T_Vals [lhs], E_BitstrLhs (acc, e :: es, segs, rho) :: rest ->
     running { c with env = rho;
                      cek = { ecxt = E_BitstrRhs (acc, lhs, [], es, segs, rho) :: rest; term = T_Expr e } }
  | T_Vals _, E_BitstrLhs _ :: _ ->
     reduction_error c "degree mismatch in bitstring segment lhs"

  | T_Vals [v], E_BitstrRhs (acc, lhs, rhs_acc, [], segs, rho) :: rest ->
     let rhs = List.rev (v :: rhs_acc) in
     begin match Bitstring_params.of_value_list rhs with
     | Error msg -> reduction_error c ("invalid bitstring segment parameters: " ^ msg)
     | Ok params ->
        let acc' = Bitstring_codec.encode_segment acc lhs params in
        lift_refs refs (finish_bitstring_segment c rho rest acc' segs)
     end
  | T_Vals [v], E_BitstrRhs (acc, lhs, rhs_acc, e :: es, segs, rho) :: rest ->
     running { c with env = rho;
                      cek = { ecxt = E_BitstrRhs (acc, lhs, v :: rhs_acc, es, segs, rho) :: rest; term = T_Expr e } }
  | T_Vals _, E_BitstrRhs _ :: _ ->
     reduction_error c "degree mismatch in bitstring segment rhs"

  (* --- Let ---
     Bind the evaluated value sequence to the let-bound variables, then evaluate
     the body.  The spec guarantees [xs] and [vs] have the same length. *)
  | T_Vals vs, E_Let (xs, rhs, rho) :: rest ->
     let rho' = bind_vars c xs vs rho in
     running { c with env = rho'; cek = { ecxt = rest; term = T_Expr rhs } }

  (* --- Case ---
     Try each clause in order via select_clause: match patterns then evaluate
     the guard.  In well-formed compiler-output Core there is always a catch-all
     clause (the compiler emits [primop match_fail(...)]), so [Ok None] is a bug. *)
  | T_Vals vs, E_Case (clauses, rho) :: rest ->
     Running (List.filter_map (fun (refs', result) ->
       match result with
       | Ok (Some (rho', body)) ->
          Some (refs', { c with env = rho'; cek = { ecxt = rest; term = T_Expr body } })
       | Ok None ->
          reduction_error c "case: no clause matched (missing catch-all in Core)"
       | Error ex ->
          Some (refs', { c with cek = { ecxt = rest; term = T_Raise ex } })
     ) (select_clause mt refs c vs rho clauses))

  (* --- Apply ---
     E_ApplyFun has evaluated the function position.  If there are no arguments,
     call immediately.  Otherwise push E_ApplyArgs and evaluate them left-to-right.
     E_ApplyArgs accumulates argument values.  When all are done, call the closure. *)
  | T_Vals [fn], E_ApplyFun ([], _rho) :: rest ->
     apply_closure refs c rest fn []
  | T_Vals [fn], E_ApplyFun (e :: es, rho) :: rest ->
     running { c with env = rho;
                      cek = { ecxt = E_ApplyArgs (fn, [], es, rho) :: rest; term = T_Expr e } }
  | T_Vals _, E_ApplyFun _ :: _ ->
     reduction_error c "degree mismatch in apply function position"

  | T_Vals [v], E_ApplyArgs (fn, acc, [], _rho) :: rest ->
     apply_closure refs c rest fn (List.rev (v :: acc))
  | T_Vals [v], E_ApplyArgs (fn, acc, e :: es, rho) :: rest ->
     running { c with env = rho;
                      cek = { ecxt = E_ApplyArgs (fn, v :: acc, es, rho) :: rest; term = T_Expr e } }
  | T_Vals _, E_ApplyArgs _ :: _ ->
     reduction_error c "degree mismatch in apply argument"

  (* --- Qualified call (inter-module) ---
     We evaluate the module and function expressions correctly (so CEK frames are
     pushed and the eval context is well-formed) but fail at the actual dispatch
     because there is no module table yet. *)
  | T_Vals [mv], E_QCallMod (fe, args, rho) :: rest ->
     running { c with env = rho;
                      cek = { ecxt = E_QCallFun (mv, args, rho) :: rest; term = T_Expr fe } }
  | T_Vals _, E_QCallMod _ :: _ ->
     reduction_error c "degree mismatch in call module position"

  | T_Vals [fv], E_QCallFun (mv, [], _rho) :: rest ->
     Call_dispatch.dispatch_call mt refs mv fv [] c rest
  | T_Vals [fv], E_QCallFun (mv, e :: es, rho) :: rest ->
     running { c with env = rho;
                      cek = { ecxt = E_QCallArgs (mv, fv, [], es, rho) :: rest; term = T_Expr e } }
  | T_Vals _, E_QCallFun _ :: _ ->
     reduction_error c "degree mismatch in call function position"

  | T_Vals [v], E_QCallArgs (mv, fv, acc, [], _rho) :: rest ->
     Call_dispatch.dispatch_call mt refs mv fv (List.rev (v :: acc)) c rest
  | T_Vals [v], E_QCallArgs (mv, fv, acc, e :: es, rho) :: rest ->
     running { c with env = rho;
                      cek = { ecxt = E_QCallArgs (mv, fv, v :: acc, es, rho) :: rest; term = T_Expr e } }
  | T_Vals _, E_QCallArgs _ :: _ ->
     reduction_error c "degree mismatch in call argument"

  (* --- Primop ---
     Accumulate argument values; fail when all arguments are ready (no primop
     implementation yet). *)
  | T_Vals [v], E_PrimOp (name, acc, [], _rho) :: rest ->
     lift_refs refs (Primops.dispatch name (List.rev (v :: acc)) c rest)
  | T_Vals [v], E_PrimOp (name, acc, e :: es, rho) :: rest ->
     running { c with env = rho;
                      cek = { ecxt = E_PrimOp (name, v :: acc, es, rho) :: rest; term = T_Expr e } }
  | T_Vals _, E_PrimOp _ :: _ ->
     reduction_error c "degree mismatch in primop argument"

  (* --- Receive ---
     The timeout expression has been evaluated.  Emit an SR_Receive request;
     the scheduler owns channel scanning and timeout/message branching. *)
  | T_Vals [timeout], E_Receive (clauses, timeout_body, rho) :: rest ->
     reduce_receive mt refs c rest rho clauses timeout_body timeout
  | T_Vals _, E_Receive _ :: _ ->
     reduction_error c "degree mismatch in receive timeout"

  (* --- ETS (scheduler frame) ---
     A process parked on an ETS operation by [Ets_bifs] re-emits the same
     [Stuck] when re-stepped, exactly like a parked receive.  All resolution
     (forced, producer, observer branching) belongs to the scheduler. *)
  | T_Vals [], (E_Ets op :: rest as ecxt) ->
     Stuck (SR_Ets { op; cont = rest }, (refs, { c with cek = { ecxt; term = T_Vals [] } }))
  | T_Vals _, E_Ets _ :: _ ->
     reduction_error c "degree mismatch in ETS frame"

  (* --- Try (success path) ---
     The protected expression completed normally.  Bind its values to the
     success variables and evaluate the in-expression. *)
  | T_Vals vs, E_Try (vars, in_exp, _catch_vars, _catch_exp, rho) :: rest ->
     let rho' = bind_vars c vars vs rho in
     running { c with env = rho'; cek = { ecxt = rest; term = T_Expr in_exp } }

  (* --- Do ---
     Sequencing: discard the current result and evaluate the next expression.
     When there are no more expressions, pass the last result outward. *)
  | T_Vals vs, E_Do ([], rho) :: rest ->
     running { c with env = rho; cek = { ecxt = rest; term = T_Vals vs } }
  | T_Vals _, E_Do (e :: es, rho) :: rest ->
     running { c with env = rho; cek = { ecxt = E_Do (es, rho) :: rest; term = T_Expr e } }

  (* --- Catch (no exception) ---
     The sub-expression completed normally; just pass the values through. *)
  | T_Vals vs, E_Catch :: rest ->
     running { c with cek = { ecxt = rest; term = T_Vals vs } }

  (* --- Maps ---
     Pairs are evaluated left-to-right; the base expression (if any) is last.
     E_MapKey : just evaluated a key; now evaluate its paired value.
     E_MapVal : just evaluated a value; either move to the next pair or
                start evaluating the base (if present) or build the final map.
     E_MapBase: just evaluated the base; fold all accumulated pairs into it. *)
  | T_Vals [k], E_MapKey (done_, op, val_e, rest_as, base_opt, rho) :: rest ->
     running { c with env = rho;
                      cek = { ecxt = E_MapVal (done_, k, op, rest_as, base_opt, rho) :: rest;
                              term = T_Expr val_e } }
  | T_Vals _, E_MapKey _ :: _ ->
     reduction_error c "degree mismatch in map key"

  | T_Vals [v], E_MapVal (done_, k, op, rest_as, base_opt, rho) :: rest ->
     let acc = (op, k, v) :: done_ in
     begin match rest_as with
     | next :: more ->
         running { c with env = rho;
                          cek = { ecxt = E_MapKey (acc, next.ma_op, next.ma_val, more, base_opt, rho) :: rest;
                                  term = T_Expr next.ma_key } }
     | [] ->
         let pairs = List.rev acc in
         begin match base_opt with
         | None ->
             let m = List.fold_left (apply_assoc_to c) [] pairs in
             running { c with env = rho; cek = { ecxt = rest; term = T_Vals [V_map m] } }
         | Some base_e ->
             running { c with env = rho;
                              cek = { ecxt = E_MapBase (pairs, rho) :: rest; term = T_Expr base_e } }
         end
     end
  | T_Vals _, E_MapVal _ :: _ ->
     reduction_error c "degree mismatch in map value"

  | T_Vals [base_v], E_MapBase (pairs, rho) :: rest ->
     begin match base_v with
     | V_map base_kvs ->
         let m = List.fold_left (apply_assoc_to c) base_kvs pairs in
         running { c with env = rho; cek = { ecxt = rest; term = T_Vals [V_map m] } }
     | _ ->
         reduction_error c "map update: base expression is not a map"
     end
  | T_Vals _, E_MapBase _ :: _ ->
     reduction_error c "degree mismatch in map base"

  (*------------------------------------------------------------------*)
  (* Exception propagation : T_Raise ex, frame :: rest               *)
  (*------------------------------------------------------------------*)

  (* E_Try intercepts the exception: bind class/reason/info to the catch
     variables and evaluate the handler expression. *)
  | T_Raise ex, E_Try (_vars, _in_exp, catch_vars, catch_exp, rho) :: rest ->
     let vals = exception_values c ex (List.length catch_vars) in
     let rho' = bind_vars c catch_vars vals rho in
     running { c with env = rho'; cek = { ecxt = rest; term = T_Expr catch_exp } }

  (* E_Catch intercepts: convert the exception to the Erlang catch-result value. *)
  | T_Raise ex, E_Catch :: rest ->
     running { c with cek = { ecxt = rest; term = T_Vals (catch_result ex) } }

  (* All other frames are skipped; the exception propagates outward. *)
  | T_Raise _, _ :: rest ->
     running { c with cek = { c.cek with ecxt = rest } }

(*------------------------------------------------------------------*)
(* Mutual recursion helpers                                          *)
(*------------------------------------------------------------------*)

(** Evaluate a guard expression to completion in a fresh empty context.
    Guards are a restricted expression subset guaranteed to terminate.
    Returns [Ok true]/[Ok false] on a boolean result, or [Error ex] if
    the guard raises an exception. *)
and eval_guard (mt : Call_dispatch.module_table) (refs : ref_env) (c : process_conf) (rho : env) (guard : expr)
    : (ref_env * (bool, raised_exception) result) list =
  let gc = { c with env = rho; cek = { ecxt = []; term = T_Expr guard } } in
  let rec loop refs gc =
    match focus gc with
    | Some gc' -> loop refs gc'
    | None ->
       match reduce mt refs gc with
       | Running rcs -> List.concat_map (fun (refs', gc') -> loop refs' gc') rcs
       | Stuck _     -> reduction_error c "guard got stuck"
       | Done (refs', gc') ->
          match gc'.cek.term with
          | T_Vals [V_atom "true"]  -> [(refs', Ok true)]
          | T_Vals [V_atom "false"] -> [(refs', Ok false)]
          | T_Raise ex              -> [(refs', Error ex)]
          | _ -> reduction_error c "guard did not return a boolean"
  in
  loop refs gc

(** Transition between bitstring segments.  [acc] already includes the last
    encoded segment.  If [segs] is empty, wrap [acc] as [V_binary]; otherwise
    push a new [E_BitstrLhs] frame for the next segment. *)
and finish_bitstring_segment c rho rest acc = function
  | [] ->
     let (bits, len_bits) = acc in
     return_val c rest (V_binary (bits, len_bits))
  | { bits_lhs; bits_rhs } :: segs ->
     Running [{ c with env = rho;
                       cek = { ecxt = E_BitstrLhs (acc, bits_rhs, segs, rho) :: rest;
                               term = T_Expr bits_lhs } }]

(** Suspend the process waiting for a network delivery.  All receive
    shapes -- including timeout 0 -- are returned as [SR_Receive] so
    the Layer 0 reducer ([big_step_many]) and the Layer 1 scheduler
    see a uniform interface.  The scheduler owns all timeout and
    message-delivery decisions. *)
and reduce_receive _mt (refs : ref_env) c rest rho clauses timeout_body timeout =
  Stuck (SR_Receive { clauses; timeout; timeout_body; rho; cont = rest }, (refs, c))

(** Try each clause in order against the value sequence [vs].
    For each matching clause, evaluate its guard.
    Returns [Ok (Some (rho', body))] on the first clause whose pattern matches
    and whose guard returns [true]; [Ok None] if no clause matches;
    [Error ex] if a guard raises. *)
and select_clause (mt : Call_dispatch.module_table) (refs : ref_env) c vs rho clauses
    : (ref_env * ((env * expr) option, raised_exception) result) list =
  let rec go refs = function
    | [] -> [(refs, Ok None)]
    | cl :: rest ->
       match match_patterns c rho cl.cp_lhs vs with
       | None -> go refs rest
       | Some bindings ->
          let rho' = extend_vars bindings rho in
          List.concat_map (fun (refs', guard_result) ->
            match guard_result with
            | Ok true  -> [(refs', Ok (Some (rho', cl.cp_rhs)))]
            | Ok false -> go refs' rest
            | Error ex -> [(refs', Error ex)]
          ) (eval_guard mt refs c rho' cl.cp_guard)
  in
  go refs clauses

(*************************)
(* BIG-STEP / EVALUATION *)
(*************************)

(** One big step: focus until no more focusing is possible, then fire one
    [reduce]. Returns a [status] -- either [Running] new confs, [Done], or
    [Stuck]. *)
let rec big_step_one (mt : Call_dispatch.module_table) (refs : ref_env) (c : process_conf)
    : (ref_env * process_conf) status =
  match focus c with
  | Some c' -> big_step_one mt refs c'
  | None    -> reduce mt refs c

(** Result of a complete evaluation run. *)
type result = { done_confs : process_conf list; stuck_confs : process_conf list }

let empty_result = { done_confs = []; stuck_confs = [] }

(** Drive a list of pending confs to completion (BFS order).
    All [Done] and [Stuck] confs accumulate in [acc]; [Running] confs are
    re-queued. *)
let rec big_step_many (mt : Call_dispatch.module_table) (pending : (ref_env * process_conf) list) (acc : result) : result =
  let step (pending', acc') (refs, c) =
    match big_step_one mt refs c with
    | Running rcs        -> (rcs @ pending', acc')
    | Done (_, c')       -> (pending', { acc' with done_confs = c' :: acc'.done_confs })
    | Stuck (_, (_, c')) -> (pending', { acc' with stuck_confs = c' :: acc'.stuck_confs })
  in
  match List.fold_left step ([], acc) pending with
  | [], acc'       -> acc'
  | pending', acc' -> big_step_many mt pending' acc'

(** Evaluate a single starting configuration to completion. *)
let run (mt : Call_dispatch.module_table) (c : process_conf) : result =
  big_step_many mt [(empty_ref_env, c)] empty_result
