open Ast

let dispatch (fun_name : string) (args : value list)
    (conf : process_conf) (rest : eval_cxt)
    : process_conf status =
  match fun_name, args with
  | "uniform", [V_int n] ->
    let result = V_int (Z.add Z.one (Z.random_int n)) in
    return_val conf rest result
  | _ ->
    failwith (Printf.sprintf "[rand_bifs] WIP: rand:%s/%d"
                fun_name (List.length args))
