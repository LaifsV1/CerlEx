open Ast

let dispatch (fun_name : string) (args : value list)
    (conf : process_conf) (rest : eval_cxt)
    : process_conf status =
  let to_float = function
    | V_int n   -> Z.to_float n
    | V_float f -> f
    | V_char c  -> float_of_int (Char.code c)
    | _         -> raise Exit
  in
  let f1 f = match args with
    | [v] -> (match to_float v with
               | x -> return_val conf rest (V_float (f x))
               | exception Exit -> raise_exn conf rest Error (V_atom "badarith"))
    | _ -> raise_exn conf rest Error (V_atom "badarith")
  in
  let f2 f = match args with
    | [v1; v2] -> (match to_float v1, to_float v2 with
                   | x, y -> return_val conf rest (V_float (f x y))
                   | exception Exit -> raise_exn conf rest Error (V_atom "badarith"))
    | _ -> raise_exn conf rest Error (V_atom "badarith")
  in
  match fun_name with
  | "pi"    -> return_val conf rest (V_float Float.pi)
  | "sin"   -> f1 sin
  | "cos"   -> f1 cos
  | "tan"   -> f1 tan
  | "asin"  -> f1 asin
  | "acos"  -> f1 acos
  | "atan"  -> f1 atan
  | "atan2" -> f2 atan2
  | "sinh"  -> f1 sinh
  | "cosh"  -> f1 cosh
  | "tanh"  -> f1 tanh
  | "asinh" -> f1 (fun x -> log (x +. sqrt (x *. x +. 1.0)))
  | "acosh" -> f1 (fun x -> log (x +. sqrt (x *. x -. 1.0)))
  | "atanh" -> f1 (fun x -> 0.5 *. log ((1.0 +. x) /. (1.0 -. x)))
  | "exp"   -> f1 exp
  | "log"   -> f1 log
  | "log2"  -> f1 Float.log2
  | "log10" -> f1 log10
  | "pow"   -> f2 ( ** )
  | "sqrt"  -> f1 sqrt
  | "erf"   -> f1 Float.erf
  | "erfc"  -> f1 Float.erfc
  | "ceil"  -> f1 ceil
  | "floor" -> f1 floor
  | "fmod"  -> f2 mod_float
  | name ->
      failwith (Printf.sprintf "[math_bifs] not implemented: math:'%s'/%d"
                  name (List.length args))
