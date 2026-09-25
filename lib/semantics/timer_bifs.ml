open Ast

let dispatch (fun_name : string) (args : value list)
    (conf : process_conf) (rest : eval_cxt)
    : process_conf status =
  match fun_name, args with
  | "sleep", [_] ->
      return_val conf rest (V_atom "ok")
  | name, argv ->
      failwith (Printf.sprintf "[timer_bifs] not implemented: timer:'%s'/%d"
                  name (List.length argv))
