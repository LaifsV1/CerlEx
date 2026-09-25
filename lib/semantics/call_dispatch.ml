(** Top-level dispatcher for qualified calls (call 'Mod':'Fun'(Args)).

    Routes by module name to the appropriate BIF implementation or to a
    user-defined module looked up in the module_table.

    Module table design
    -------------------
    The module_table maps module name strings to per-module function
    tables (module_def).  It is populated externally by the tool front-end
    when it loads .core files, and threaded through the reduction engine
    via Reductions.reduce.

    A module_def is a [closure FnameMap.t]: the same structure used by
    env.funs inside a running process.  FnameMap keys are {fn_name; fn_arity}
    pairs, so functions with the same name but different arities are
    distinguished automatically.

    Built-in modules (erlang, io, math, timer, rand) are handled directly by
    the routing match and are NOT stored in the module table.  The maps module
    is NOT a built-in — load otp_stdlib/maps.core instead.

    User-defined module application is handled here by directly constructing
    the next CEK state (binding arguments to formal parameters and evaluating
    the closure body).  This keeps call_dispatch.ml independent of
    reductions.ml and avoids a circular module dependency:
      call_dispatch -> erlang_bifs / maps_bifs (no reductions dependency)
      reductions    -> call_dispatch            (one-way)

    @author Yu-Yang Lin
    @since 2026-05-11
 *)

open Ast
open Syntax.Core_ast

(* -------------------------------------------------------------------- *)
(* Module table                                                          *)
(* -------------------------------------------------------------------- *)

module StringMap = Map.Make(String)

(** Per-module function table: maps fname (name + arity) to closure.
    Same structure as env.funs used inside a running process. *)
type module_def = closure FnameMap.t

(** Global module table: maps module name -> module_def.
    Built-in modules (erlang, maps) are routed before this table is
    consulted and so do not appear in it. *)
type module_table = module_def StringMap.t

let empty_module_table : module_table = StringMap.empty

(** Add or replace a module's function definitions in the table. *)
let add_module (name : string) (def : module_def) (mt : module_table)
    : module_table =
  StringMap.add name def mt

(* -------------------------------------------------------------------- *)
(* User-defined closure application                                      *)
(* -------------------------------------------------------------------- *)

(** Apply a user-defined closure to args by constructing the next CEK state:
    bind each formal parameter to its argument value in the closure's captured
    environment, then set the current term to the closure body.

    This replicates the core logic of Reductions.apply_closure without calling
    back into reductions.ml, keeping the dependency graph acyclic. *)
let apply_user_closure
    (conf : process_conf) (rest : eval_cxt)
    (clo : closure) (args : value list)
    : process_conf status =
  let arity = List.length clo.clo_vars in
  let nargs = List.length args in
  if arity <> nargs then
    failwith (Printf.sprintf
                "[call_dispatch] arity mismatch: expected %d argument(s), got %d"
                arity nargs)
  else
    let vars' =
      List.fold_left2
        (fun acc x v -> VarMap.add x v acc)
        clo.clo_env.vars clo.clo_vars args
    in
    let env' = { clo.clo_env with vars = vars' } in
    Running [{ conf with env = env'; cek = { ecxt = rest; term = T_Expr clo.clo_body } }]

(* -------------------------------------------------------------------- *)
(* Main dispatch                                                         *)
(* -------------------------------------------------------------------- *)

(** Dispatch a qualified call [call 'Mod':'Fun'(Args)].

    mod_val and fun_val are the fully-evaluated module and function
    expressions (expected to be V_atom values).  args are the evaluated
    argument values, left-to-right.  conf is the current process
    configuration.  rest is the remaining evaluation context after the call
    site, i.e. the continuation into which the return value is placed. *)
let dispatch_call
    (mt : module_table)
    (refs : ref_env)
    (mod_val : value)
    (fun_val : value)
    (args : value list)
    (conf : process_conf)
    (rest : eval_cxt)
    : (ref_env * process_conf) status =
  let lookup mod_name fn_name arity =
    match StringMap.find_opt mod_name mt with
    | None     -> None
    | Some def -> FnameMap.find_opt { fn_name; fn_arity = arity } def
  in
  match mod_val, fun_val with
  | V_atom mod_name, V_atom fun_name ->
     begin match mod_name with
     | "erlang" -> Erlang_bifs.dispatch_r lookup refs fun_name args conf rest
     | "maps"   -> lift_refs refs (Maps_bifs.dispatch  fun_name args conf rest)
     | "io"     -> lift_refs refs (Io_bifs.dispatch    fun_name args conf rest)
     | "math"   -> lift_refs refs (Math_bifs.dispatch  fun_name args conf rest)
     | "timer"  -> lift_refs refs (Timer_bifs.dispatch fun_name args conf rest)
     | "rand"   -> lift_refs refs (Rand_bifs.dispatch  fun_name args conf rest)
     | "ets"    -> lift_refs refs (Ets_bifs.dispatch   fun_name args conf rest)
     | _ ->
        let arity = List.length args in
        begin match lookup mod_name fun_name arity with
        | None ->
           failwith (Printf.sprintf
                       "[call_dispatch] WIP: unknown module '%s' \
                        (not a built-in and not in the module table)"
                       mod_name)
        | Some clo ->
           lift_refs refs (apply_user_closure conf rest clo args)
        end
     end
  | _ ->
     failwith "[call_dispatch] module and function expressions must evaluate to atoms"
