(** Implementations of Core Erlang primops.

    Primops are compiler-internal operations identified by an unqualified name
    (no module).  Unlike [erlang:X] BIF calls, primops may directly read or
    write [process_conf] fields and may return zero or multiple values.

    [return_vals] is used instead of [return_val] because primops like
    [recv_peek_message] return a two-value sequence [<Bool, Msg>], and
    [remove_message] returns an empty sequence [<>].

    Tier-3 primops ([recv_wait_timeout], [recv_next]) require either the
    BEAM save pointer ([msg.save], modelled per-receive-evaluation; not yet
    in [process_conf]) or a global scheduler action; they return [Stuck]
    for now.  See notes/recv_primops_design.md and
    notes/recv_primops_authoritative_refs.md.

    References:
    - Core Erlang 1.0.3 specification (see notes/core_erlang-1.0.3.pdf),
      sections on exceptions and receive.
    - OTP ERTS erlang module (erlang:raise/3 and exception classes):
      https://www.erlang.org/doc/apps/erts/erlang.html
    - OTP error/exception model:
      https://www.erlang.org/doc/system/errors.html

    @author Yu-Yang Lin
    @since 2026-05-11
 *)

open Ast


(* -------------------------------------------------------------------- *)
(* Dispatch                                                              *)
(* -------------------------------------------------------------------- *)

let dispatch (prim_name : string) (args : value list)
    (conf : process_conf) (rest : eval_cxt)
    : process_conf status =
  match prim_name, args with

  (* --- Exception raising -------------------------------------------- *)

  (* [match_fail(Reason)] raises a runtime error with the reason supplied
     by the compiler -- e.g. [{case_clause, V}] or [{function_clause, Args}].
     The reason is a fully-evaluated value by the time dispatch is called. *)
  | "match_fail", [reason] ->
     raise_exn conf rest Error reason

  (* [raise(Class, Reason, Stacktrace)] raises an explicit exception.
     All three arguments are fully-evaluated values from the source program.
     This is the underlying mechanism for [erlang:raise/3].
     See: https://www.erlang.org/doc/apps/erts/erlang.html#raise/3 *)
  | "raise", [V_atom cls_str; reason; info] ->
     let class_ = match cls_str with
       | "error" -> Error
       | "exit"  -> Exit
       | "throw" -> Throw
       | s -> failwith ("[primops] unknown exception class in raise: '" ^ s ^ "'")
     in
     let ex = { class_; reason; info } in
     Running [{ conf with cek = { ecxt = rest; term = T_Raise ex } }]

  (* [exc_trace(Info)] / [build_stacktrace(Info)] return the current stack
     trace.  We have no stack trace structure; return [] as a placeholder. *)
  | "exc_trace",        [_info] -> return_vals conf rest [V_nil]
  | "build_stacktrace", [_info] -> return_vals conf rest [V_nil]

  (* --- Receive protocol --------------------------------------------- *)

  (* The four EEP-52 receive primops are intentionally unsupported.
     [Core_normalise.Recv_normalise] rewrites every OTP-compiled receive to
     [Expr_receive] before evaluation, so these arms are unreachable on any
     normalised input.  Supporting the native primop path would require
     modelling a per-channel analogue of the BEAM save pointer; deferred. *)
  | "recv_peek_message", [] ->
     failwith "[WIP] recv_peek_message: use Expr_receive; primop form not supported"
  | "remove_message", [] ->
     failwith "[WIP] remove_message: use Expr_receive; primop form not supported"
  | "recv_next", [] ->
     failwith "[WIP] recv_next: use Expr_receive; primop form not supported"
  | "recv_wait_timeout", [_] ->
     failwith "[WIP] recv_wait_timeout: use Expr_receive; primop form not supported"

  (* --- Binary -------------------------------------------------------- *)
  | "bs_init_writable", _ ->
     failwith "[primops] WIP: bs_init_writable not yet implemented"

  (* --- Unknown ------------------------------------------------------- *)
  | name, argv ->
     failwith (Printf.sprintf "[primops] not implemented: primop '%s'/%d"
                 name (List.length argv))
