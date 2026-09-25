(** [ets:*] BIF surface: argument validation only.

    ETS operations read and write scheduler-owned shared state
    ([network_conf.ets]), which is invisible at Layer 0 -- so, like [!] and
    [spawn], every ETS operation returns [Stuck] and is resolved by the
    scheduler: [maximise] resolves the forced/producer cases (unnamed [new],
    owner-writes, [delete], init-case named [new]), [schedule] the observers
    ([lookup], non-owner [insert]).  See notes/ets_plan.md (deferred-op
    scheme, 2026-07-06).

    The op payload is carried both in [SR_Ets] (used when the scheduler can
    resolve immediately) and in an [E_Ets] frame left on the context, so a
    settled process re-emits the same [Stuck] when re-stepped in a later
    round -- exactly like [E_Receive].

    v0 is deliberately partial, and its partiality is explicit: anything
    outside the supported fragment kills the whole exploration with [failwith] --
    no answer rather than a possibly-wrong answer.  It must never be folded
    into per-trace exception counts, otherwise the [done] line would report
    plausible-but-wrong numbers. *)

open Ast

let unsupported (what : string) : 'a =
  failwith (Printf.sprintf "[ets] unsupported in v0: %s (see notes/ets_plan.md)" what)

(** Park the process on [op]: [SR_Ets] for the scheduler, [E_Ets] on the
    context for idempotent re-stepping. *)
let stuck_on (conf : process_conf) (rest : eval_cxt) (op : ets_op)
    : process_conf status =
  Stuck (SR_Ets { op; cont = rest },
         { conf with cek = { ecxt = E_Ets op :: rest; term = T_Vals [] } })

(** A table argument must be a tid or a (named-table) atom; anything else is
    an immediate local badarg, no shared state consulted. *)
let is_tab = function V_ets_tid _ | V_atom _ -> true | _ -> false

(** Validate an [ets:new/2] options list.  Returns [named].  v0 accepts only
    [set] (the default type), the access atoms (accepted and ignored: access
    control is not modelled), [named_table], and [{keypos,1}].  Everything
    else kills the exploration as unsupported. *)
let rec parse_new_opts (conf : process_conf) (rest : eval_cxt) (named : bool)
    (opts : value) : (bool, process_conf status) result =
  match opts with
  | V_nil -> Ok named
  | V_cons (opt, tl) ->
    begin match opt with
    | V_atom "set" -> parse_new_opts conf rest named tl
    | V_atom ("public" | "protected" | "private") ->
      parse_new_opts conf rest named tl
    | V_atom "named_table" -> parse_new_opts conf rest true tl
    | V_tuple [V_atom "keypos"; V_int n] when Z.equal n Z.one ->
      parse_new_opts conf rest named tl
    | V_tuple [V_atom "keypos"; _] -> unsupported "ets:new keypos =/= 1"
    | V_atom ("ordered_set" | "bag" | "duplicate_bag") ->
      unsupported "ets:new non-set table type"
    | V_atom a -> unsupported (Printf.sprintf "ets:new option '%s'" a)
    | V_tuple (V_atom a :: _) -> unsupported (Printf.sprintf "ets:new option {%s,...}" a)
    | _ -> Error (raise_exn conf rest Error (V_atom "badarg"))
    end
  | _ -> Error (raise_exn conf rest Error (V_atom "badarg"))

let dispatch (fun_name : string) (args : value list)
    (conf : process_conf) (rest : eval_cxt) : process_conf status =
  match fun_name, args with
  | "new", [V_atom tname; opts] ->
    begin match parse_new_opts conf rest false opts with
    | Ok named  -> stuck_on conf rest (Ets_new { tname; named })
    | Error err -> err
    end
  | "new", [_; _] -> raise_exn conf rest Error (V_atom "badarg")

  | "insert", [tab; obj] when is_tab tab ->
    begin match obj with
    | V_tuple (_ :: _) -> stuck_on conf rest (Ets_insert { tab; obj })
    | V_nil | V_cons _ -> unsupported "ets:insert of an object list"
    | _ -> raise_exn conf rest Error (V_atom "badarg")
    end
  | "insert", [_; _] -> raise_exn conf rest Error (V_atom "badarg")

  | "lookup", [tab; key] when is_tab tab ->
    stuck_on conf rest (Ets_lookup { tab; key; elem = None })
  | "lookup", [_; _] -> raise_exn conf rest Error (V_atom "badarg")

  | "lookup_element", [tab; key; V_int pos]
    when is_tab tab && Z.geq pos Z.one ->
    stuck_on conf rest (Ets_lookup { tab; key; elem = Some (Z.to_int pos) })
  | "lookup_element", [_; _; _] -> raise_exn conf rest Error (V_atom "badarg")

  | "delete", [tab] when is_tab tab ->
    stuck_on conf rest (Ets_delete { tab })
  | "delete", [_] -> raise_exn conf rest Error (V_atom "badarg")
  | "delete", [_; _] -> unsupported "ets:delete/2 (key delete)"

  | f, args ->
    unsupported (Printf.sprintf "ets:%s/%d" f (List.length args))
