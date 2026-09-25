(** Normalise the OTP/EEP-52 receive lowering back to high-level
    [Expr_receive].

    Background.  Since OTP 23 (EEP 52) the compiler always lowers source
    [receive ... end] to a Core Erlang primop loop of a stable shape (see
    [notes/recv_primops_design.md] and [notes/recv_primops_authoritative_refs.md]).
    The 1.0.3 spec rejects decomposing receive into mailbox operations; this
    pass undoes the lowering so the rest of the tool can operate on
    [Expr_receive] uniformly.

    This recogniser is intentionally written for compiler output: it expects
    the canonical Core Erlang shape emitted by OTP's receive lowering.  It is
    not a general-purpose simplifier for arbitrary hand-written Core Erlang,
    unless that hand-written Core follows the same lowering conventions closely
    enough to be indistinguishable from compiler output.

    Recognised shape (with all annotations stripped by the parser).

    Outer wrap:
    {v
        letrec 'recv$^N'/0 = fun () -> <BODY>
        in apply 'recv$^N'/0 ()
    v}

    Variant A (source receive has message clauses):
    {v
        let <B, M> = primop 'recv_peek_message'() in
        case B of
          <'true'>  when 'true' -> <CLAUSE-MATCH>
          <'false'> when 'true' -> <WAIT-PART>
        end
    v}

    Variant B (source receive has only an after-body):
    {v
        <WAIT-PART>
    v}

    <CLAUSE-MATCH> is either A1 (single catch-all):
    {v
        do primop 'remove_message'() <Body>
    v}
    or A2 (multi-clause with compiler-generated no-match fallthrough):
    {v
        case M of
          <Pat_i> when <Guard_i> -> do primop 'remove_message'() <Body_i>
          ...
          <Other>  when 'true'   -> do primop 'recv_next'() apply 'recv$^N'/0()
        end
    v}

    Bare-remove variant: when a clause body is pure and its result is
    discarded (the receive appears as the first expression in a [do]
    sequence), OTP elides the body entirely and emits just:
    {v
        primop 'remove_message'()
    v}
    [remove_message] returns ['ok'], so stripping it and reconstructing
    the body as ['ok'] is semantically correct.  This variant can appear
    in both A1 and A2 positions.

    <WAIT-PART>:
    {v
        let <T> = primop 'recv_wait_timeout'(<TE>) in
        case T of
          <'true'>  when 'true' -> <TB>
          <'false'> when 'true' -> apply 'recv$^N'/0()
        end
    v}

    If everything matches, the normaliser produces
    [Expr_receive { rcv_pat = clauses; tm_after = TE; tm_body = TB }],
    where [clauses] are the user clauses (the synthetic <Other> fallthrough
    is dropped).  Any deviation from this shape leaves the expression
    untouched and we fall through to the existing primop dispatch
    (currently [Stuck]). *)

open Syntax.Core_ast

(* -------------------------------------------------------------------- *)
(* Small predicates                                                      *)
(* -------------------------------------------------------------------- *)

let recv_loop_prefix = "recv$^"

let is_recv_loop_name (s : string) : bool =
  let n = String.length recv_loop_prefix in
  String.length s >= n && String.sub s 0 n = recv_loop_prefix

let is_atom_lit (a : string) : expr -> bool = function
  | Expr_literal (Lit_atom x) -> x = a
  | _ -> false

let is_true_guard (e : expr) : bool = is_atom_lit "true" e

let is_recv_loop_apply (loop_name : string) : expr -> bool = function
  | Expr_apply { fn_name = Expr_fname f; fn_args = [] } ->
     f.fn_name = loop_name && f.fn_arity = 0
  | _ -> false

let is_primop (name : string) : expr -> bool = function
  | Expr_primop { pop_name; pop_args = [] } -> pop_name = name
  | _ -> false

(** Find the clause whose only pattern is a literal atom equal to [a]. *)
let find_atom_clause (a : string) (cls : clause list) : clause option =
  List.find_opt
    (fun cl ->
      match cl.cp_lhs with
      | [Pat_lit (Lit_atom x)] -> x = a
      | _ -> false)
    cls

(* -------------------------------------------------------------------- *)
(* Variable substitution helpers                                         *)
(* -------------------------------------------------------------------- *)

(** Collect all variables bound by a pattern (for shadowing checks). *)
let rec pat_vars : pattern -> var_name list = function
  | Pat_var_name v     -> [v]
  | Pat_alias (v, sub) -> v :: pat_vars sub
  | Pat_tuple ps | Pat_list ps -> List.concat_map pat_vars ps
  | Pat_cons (ps, tl)  -> List.concat_map pat_vars ps @ pat_vars tl
  | Pat_bitstring segs -> List.concat_map (fun bp -> pat_vars bp.bits_pat_lhs) segs
  | Pat_map ps         -> List.concat_map (fun mp -> pat_vars mp.mpa_pat) ps
  | Pat_lit _          -> []

let pat_list_vars (ps : pattern list) : var_name list =
  List.concat_map pat_vars ps

(** [subst_var old_v new_v e] replaces free occurrences of [Expr_var old_v]
    with [Expr_var new_v] in [e], respecting variable shadowing in all binders. *)
let rec subst_var (old_v : var_name) (new_v : var_name) (e : expr) : expr =
  if old_v = new_v then e
  else match e with
  | Expr_var v -> if v = old_v then Expr_var new_v else e
  | Expr_literal _ | Expr_fname _ -> e
  | Expr_val_list es -> Expr_val_list (List.map (subst_var old_v new_v) es)
  | Expr_tuple es    -> Expr_tuple    (List.map (subst_var old_v new_v) es)
  | Expr_list  es    -> Expr_list     (List.map (subst_var old_v new_v) es)
  | Expr_cons (es, tl) ->
     Expr_cons (List.map (subst_var old_v new_v) es, subst_var old_v new_v tl)
  | Expr_binary segs ->
     Expr_binary (List.map (fun bs ->
       { bits_lhs = subst_var old_v new_v bs.bits_lhs;
         bits_rhs = List.map (subst_var old_v new_v) bs.bits_rhs }) segs)
  | Expr_let lb ->
     let lb_expr' = subst_var old_v new_v lb.lb_expr in
     let lb_rhs'  =
       if List.mem old_v lb.lb_lhs then lb.lb_rhs
       else subst_var old_v new_v lb.lb_rhs
     in
     Expr_let { lb with lb_expr = lb_expr'; lb_rhs = lb_rhs' }
  | Expr_letrec lr ->
     (* fn_name fields are fname (atom+arity), not var_name -- no var shadowing *)
     Expr_letrec {
       lrb_lhs = List.map (fun fd ->
           { fd with fd_body =
               if List.mem old_v fd.fd_body.fe_vars then fd.fd_body
               else { fd.fd_body with fe_body =
                        subst_var old_v new_v fd.fd_body.fe_body } }) lr.lrb_lhs;
       lrb_rhs = subst_var old_v new_v lr.lrb_rhs }
  | Expr_case c ->
     Expr_case { case_exp = subst_var old_v new_v c.case_exp;
                 case_pat = List.map (subst_var_clause old_v new_v) c.case_pat }
  | Expr_apply { fn_name; fn_args } ->
     Expr_apply { fn_name = subst_var old_v new_v fn_name;
                  fn_args = List.map (subst_var old_v new_v) fn_args }
  | Expr_qualified_call qc ->
     Expr_qualified_call { qc_mod  = subst_var old_v new_v qc.qc_mod;
                           qc_fun  = subst_var old_v new_v qc.qc_fun;
                           qc_args = List.map (subst_var old_v new_v) qc.qc_args }
  | Expr_fun fe ->
     if List.mem old_v fe.fe_vars then e
     else Expr_fun { fe with fe_body = subst_var old_v new_v fe.fe_body }
  | Expr_receive r ->
     Expr_receive { rcv_pat  = List.map (subst_var_clause old_v new_v) r.rcv_pat;
                    tm_after = subst_var old_v new_v r.tm_after;
                    tm_body  = subst_var old_v new_v r.tm_body }
  | Expr_primop p ->
     Expr_primop { p with pop_args = List.map (subst_var old_v new_v) p.pop_args }
  | Expr_try t ->
     Expr_try { t with
       tc_exp   = subst_var old_v new_v t.tc_exp;
       tc_in    = (if List.mem old_v t.tc_vars       then t.tc_in
                   else subst_var old_v new_v t.tc_in);
       tc_catch = (if List.mem old_v t.tc_catch_vars then t.tc_catch
                   else subst_var old_v new_v t.tc_catch) }
  | Expr_do es    -> Expr_do   (List.map (subst_var old_v new_v) es)
  | Expr_catch e' -> Expr_catch (subst_var old_v new_v e')
  | Expr_map m ->
     Expr_map { map_base   = Option.map (subst_var old_v new_v) m.map_base;
                map_assocs = List.map (fun a ->
                  { a with ma_key = subst_var old_v new_v a.ma_key;
                           ma_val = subst_var old_v new_v a.ma_val }) m.map_assocs }

and subst_var_clause (old_v : var_name) (new_v : var_name) (cl : clause) : clause =
  if List.mem old_v (pat_list_vars cl.cp_lhs) then cl
  else { cl with
    cp_guard = subst_var old_v new_v cl.cp_guard;
    cp_rhs   = subst_var old_v new_v cl.cp_rhs }

(** If the clause's single-pattern list binds the whole message to a variable,
    return that variable name; otherwise [None].  Used to identify which
    variable should replace [msg_var] in guards and rhs after normalisation
    removes the peek let-binding. *)
let clause_whole_msg_var (cl : clause) : var_name option =
  match cl.cp_lhs with
  | [Pat_var_name v]   -> Some v
  | [Pat_alias (v, _)] -> Some v
  | _                  -> None

(** After [rewrite_user_clause] strips [remove_message], replace free
    occurrences of the peek variable [msg_var] with the pattern-bound
    variable in the clause's guard and rhs. *)
let fix_msg_var_refs (msg_var : var_name) (c : clause) : clause =
  match clause_whole_msg_var c with
  | Some pv when pv <> msg_var ->
     { c with cp_guard = subst_var msg_var pv c.cp_guard;
              cp_rhs   = subst_var msg_var pv c.cp_rhs }
  | _ -> c

(* -------------------------------------------------------------------- *)
(* Sub-recognisers                                                       *)
(* -------------------------------------------------------------------- *)

(** Match the WAIT-PART.

    [let <T> = primop 'recv_wait_timeout'(TE) in
      case T of
        <'true'>  when 'true' -> TB
        <'false'> when 'true' -> apply 'recv$^N'/0()
      end].

    On success returns [Some (TE, TB)]. *)
let match_wait_part (loop_name : string) : expr -> (expr * expr) option = function
  | Expr_let { lb_lhs = [t_var];
               lb_expr = Expr_primop { pop_name = "recv_wait_timeout";
                                       pop_args = [te] };
               lb_rhs = Expr_case { case_exp = Expr_var t_var2;
                                    case_pat = clauses } }
    when t_var = t_var2 ->
     let true_cl  = find_atom_clause "true"  clauses in
     let false_cl = find_atom_clause "false" clauses in
     begin match true_cl, false_cl with
     | Some tcl, Some fcl
          when is_true_guard tcl.cp_guard
            && is_true_guard fcl.cp_guard
            && is_recv_loop_apply loop_name fcl.cp_rhs ->
        Some (te, tcl.cp_rhs)
     | _ -> None
     end
  | _ -> None

(** Match the compiler-generated no-match fallthrough clause:
    [<Other> when 'true' -> do primop 'recv_next'() apply 'recv$^N'/0()]. *)
let is_fallthrough_clause (loop_name : string) (cl : clause) : bool =
  (match cl.cp_lhs with [Pat_var_name _] -> true | _ -> false)
  && is_true_guard cl.cp_guard
  &&
  begin match cl.cp_rhs with
  | Expr_do [next_primop; tail_apply] ->
     is_primop "recv_next" next_primop
     && is_recv_loop_apply loop_name tail_apply
  | _ -> false
  end

(** Strip [do primop 'remove_message'() <body>] -> [<body>].

    OTP also emits bare [primop 'remove_message'()] (no do-wrapper) when the
    receive result is discarded and the clause body is pure.  In that position
    OTP replaces the body with [remove_message]'s own return value ([ok]), so
    stripping the primop and returning ['ok'] is semantically correct. *)
let strip_remove_message : expr -> expr option = function
  | Expr_do [rm_primop; body] when is_primop "remove_message" rm_primop ->
     Some body
  | Expr_primop { pop_name = "remove_message"; pop_args = [] } ->
     Some (Expr_literal (Lit_atom "ok"))
  | _ -> None

(** Convert a user clause [<Pat> when G -> do remove_message() <Body>] into
    [<Pat> when G -> <Body>]. *)
let rewrite_user_clause (cl : clause) : clause option =
  match strip_remove_message cl.cp_rhs with
  | Some body -> Some { cl with cp_rhs = body }
  | None -> None

(** Match CLAUSE-MATCH form A1 -- single catch-all.

    The single match is [do primop 'remove_message'() <body>]; we
    synthesise a one-clause receive [<MsgVar> when 'true' -> <body>]. *)
let match_clause_match_a1 (msg_var : var_name) (e : expr) : clause list option =
  match strip_remove_message e with
  | Some body ->
     Some [{ cp_lhs = [Pat_var_name msg_var];
             cp_guard = Expr_literal (Lit_atom "true");
             cp_rhs = body }]
  | None -> None

(** Match CLAUSE-MATCH form A2 -- inner [case M of ...].

    The final clause is the compiler-generated [<Other> when 'true' ->
    do primop 'recv_next'() apply 'recv$^N'/0()] fallthrough *iff* the user's
    clauses were not exhaustive.  When the user wrote an exhaustive catch-all
    (e.g. [Other -> ...]), the compiler omits the synthetic fallthrough and
    emits all clauses as user clauses with [do remove_message() <body>]
    bodies.  We accept both shapes. *)
let match_clause_match_a2 (loop_name : string) (msg_var : var_name)
    : expr -> clause list option = function
  | Expr_case { case_exp = Expr_var v; case_pat = clauses } when v = msg_var ->
     let user_clauses =
       match List.rev clauses with
       | last :: rest_rev when is_fallthrough_clause loop_name last ->
          List.rev rest_rev                       (* drop synthetic fallthrough *)
       | _ ->
          clauses                                  (* user-exhaustive: keep all *)
     in
     let rec rewrite_all = function
       | [] -> Some []
       | c :: cs ->
          begin match rewrite_user_clause c, rewrite_all cs with
          | Some c', Some cs' -> Some (fix_msg_var_refs msg_var c' :: cs')
          | _ -> None
          end
     in
     rewrite_all user_clauses
  | _ -> None

(** Match the recv-loop BODY: either Variant A (peek+match+wait-part) or
    Variant B (just the wait part).  Returns
    [Some (clauses, timeout_expr, timeout_body)] on success. *)
let match_recv_body (loop_name : string) (body : expr)
    : (clause list * expr * expr) option =
  match body with
  | Expr_let { lb_lhs = [_b_var; m_var];
               lb_expr = Expr_primop { pop_name = "recv_peek_message";
                                       pop_args = [] };
               lb_rhs = Expr_case { case_exp = Expr_var b_var2;
                                    case_pat = bool_clauses } }
    when _b_var = b_var2 ->
     let true_cl  = find_atom_clause "true"  bool_clauses in
     let false_cl = find_atom_clause "false" bool_clauses in
     begin match true_cl, false_cl with
     | Some tcl, Some fcl
          when is_true_guard tcl.cp_guard
            && is_true_guard fcl.cp_guard ->
        let clauses_opt =
          match match_clause_match_a1 m_var tcl.cp_rhs with
          | Some cs -> Some cs
          | None    -> match_clause_match_a2 loop_name m_var tcl.cp_rhs
        in
        let wait_opt = match_wait_part loop_name fcl.cp_rhs in
        begin match clauses_opt, wait_opt with
        | Some cs, Some (te, tb) -> Some (cs, te, tb)
        | _ -> None
        end
     | _ -> None
     end
  | _ ->
     begin match match_wait_part loop_name body with
     | Some (te, tb) -> Some ([], te, tb)
     | None -> None
     end

(* -------------------------------------------------------------------- *)
(* Top-level recogniser                                                  *)
(* -------------------------------------------------------------------- *)

(** Try to normalise one expression: if it matches the EEP-52 lowering
    shape, return [Some Expr_receive { ... }]; otherwise [None]. *)
let try_normalise_recv : expr -> expr option = function
  | Expr_letrec {
        lrb_lhs =
          [{ fd_name = { fn_name = loop_name; fn_arity = 0 };
             fd_body = { fe_vars = []; fe_body = body } }];
        lrb_rhs = rhs }
    when is_recv_loop_name loop_name
      && is_recv_loop_apply loop_name rhs ->
     begin match match_recv_body loop_name body with
     | Some (clauses, te, tb) ->
        Some (Expr_receive { rcv_pat = clauses;
                             tm_after = te;
                             tm_body = tb })
     | None -> None
     end
  | _ -> None

(* -------------------------------------------------------------------- *)
(* Recursive walk over the whole AST                                     *)
(* -------------------------------------------------------------------- *)

let rec normalise_expr (e : expr) : expr =
  match try_normalise_recv e with
  | Some e' -> normalise_expr e'      (* recurse into the rewritten Expr_receive's parts *)
  | None    -> map_subexprs e

and map_subexprs (e : expr) : expr =
  match e with
  | Expr_var _ | Expr_literal _ | Expr_fname _ -> e
  | Expr_val_list es -> Expr_val_list (List.map normalise_expr es)
  | Expr_tuple es    -> Expr_tuple    (List.map normalise_expr es)
  | Expr_list  es    -> Expr_list     (List.map normalise_expr es)
  | Expr_cons (es, tl) ->
     Expr_cons (List.map normalise_expr es, normalise_expr tl)
  | Expr_binary segs ->
     Expr_binary (List.map normalise_bitstring segs)
  | Expr_let lb ->
     Expr_let { lb with lb_expr = normalise_expr lb.lb_expr;
                        lb_rhs  = normalise_expr lb.lb_rhs }
  | Expr_letrec lr ->
     Expr_letrec {
         lrb_lhs = List.map normalise_fun_def lr.lrb_lhs;
         lrb_rhs = normalise_expr lr.lrb_rhs }
  | Expr_case c ->
     Expr_case { case_exp = normalise_expr c.case_exp;
                 case_pat = List.map normalise_clause c.case_pat }
  | Expr_apply { fn_name; fn_args } ->
     Expr_apply { fn_name = normalise_expr fn_name;
                  fn_args = List.map normalise_expr fn_args }
  | Expr_qualified_call qc ->
     Expr_qualified_call { qc_mod  = normalise_expr qc.qc_mod;
                           qc_fun  = normalise_expr qc.qc_fun;
                           qc_args = List.map normalise_expr qc.qc_args }
  | Expr_fun fe -> Expr_fun (normalise_fun_expr fe)
  | Expr_receive r ->
     Expr_receive { rcv_pat  = List.map normalise_clause r.rcv_pat;
                    tm_after = normalise_expr r.tm_after;
                    tm_body  = normalise_expr r.tm_body }
  | Expr_primop p ->
     Expr_primop { p with pop_args = List.map normalise_expr p.pop_args }
  | Expr_try t ->
     Expr_try { t with tc_exp   = normalise_expr t.tc_exp;
                       tc_in    = normalise_expr t.tc_in;
                       tc_catch = normalise_expr t.tc_catch }
  | Expr_do es   -> Expr_do (List.map normalise_expr es)
  | Expr_catch e -> Expr_catch (normalise_expr e)
  | Expr_map m ->
     Expr_map { map_base   = Option.map normalise_expr m.map_base;
                map_assocs = List.map (fun a ->
                  { a with ma_key = normalise_expr a.ma_key;
                           ma_val = normalise_expr a.ma_val }) m.map_assocs }

and normalise_clause (cl : clause) : clause =
  { cl with cp_guard = normalise_expr cl.cp_guard;
            cp_rhs   = normalise_expr cl.cp_rhs }

and normalise_fun_expr (fe : fun_expr) : fun_expr =
  { fe with fe_body = normalise_expr fe.fe_body }

and normalise_fun_def (fd : fun_def) : fun_def =
  { fd with fd_body = normalise_fun_expr fd.fd_body }

and normalise_bitstring (bs : bitstring) : bitstring =
  { bits_lhs = normalise_expr bs.bits_lhs;
    bits_rhs = List.map normalise_expr bs.bits_rhs }

(** Run the normaliser over every function definition in a module. *)
let normalise_module (m : Syntax.Core_ast.t) : Syntax.Core_ast.t =
  { m with m_defs = List.map normalise_fun_def m.m_defs }

(* -------------------------------------------------------------------- *)
(* Diagnostic helpers -- counting receive primops before/after.          *)
(* -------------------------------------------------------------------- *)

let recv_primop_names =
  ["recv_peek_message"; "recv_next"; "remove_message"; "recv_wait_timeout"]

let rec count_recv_primops (e : expr) : int =
  let here =
    match e with
    | Expr_primop { pop_name; _ } when List.mem pop_name recv_primop_names -> 1
    | _ -> 0
  in
  here + List.fold_left ( + ) 0 (List.map count_recv_primops (subexprs_of e))

and subexprs_of (e : expr) : expr list =
  match e with
  | Expr_var _ | Expr_literal _ | Expr_fname _ -> []
  | Expr_val_list es | Expr_tuple es | Expr_list es | Expr_do es -> es
  | Expr_cons (es, tl) -> tl :: es
  | Expr_binary segs ->
     List.concat_map (fun bs -> bs.bits_lhs :: bs.bits_rhs) segs
  | Expr_let lb     -> [lb.lb_expr; lb.lb_rhs]
  | Expr_letrec lr  ->
     lr.lrb_rhs :: List.map (fun fd -> fd.fd_body.fe_body) lr.lrb_lhs
  | Expr_case c     ->
     c.case_exp :: List.concat_map (fun cl -> [cl.cp_guard; cl.cp_rhs]) c.case_pat
  | Expr_apply { fn_name; fn_args } -> fn_name :: fn_args
  | Expr_qualified_call qc -> qc.qc_mod :: qc.qc_fun :: qc.qc_args
  | Expr_fun fe     -> [fe.fe_body]
  | Expr_receive r  ->
     r.tm_after :: r.tm_body
     :: List.concat_map (fun cl -> [cl.cp_guard; cl.cp_rhs]) r.rcv_pat
  | Expr_primop p   -> p.pop_args
  | Expr_try t      -> [t.tc_exp; t.tc_in; t.tc_catch]
  | Expr_catch e    -> [e]
  | Expr_map m      ->
     let kvs = List.concat_map (fun a -> [a.ma_key; a.ma_val]) m.map_assocs in
     (match m.map_base with None -> kvs | Some b -> b :: kvs)

let rec count_expr_receive (e : expr) : int =
  let here = match e with Expr_receive _ -> 1 | _ -> 0 in
  here + List.fold_left ( + ) 0 (List.map count_expr_receive (subexprs_of e))

let count_recv_primops_in_module (m : Syntax.Core_ast.t) : int =
  List.fold_left ( + ) 0
    (List.map (fun fd -> count_recv_primops fd.fd_body.fe_body) m.m_defs)

let count_expr_receive_in_module (m : Syntax.Core_ast.t) : int =
  List.fold_left ( + ) 0
    (List.map (fun fd -> count_expr_receive fd.fd_body.fe_body) m.m_defs)
