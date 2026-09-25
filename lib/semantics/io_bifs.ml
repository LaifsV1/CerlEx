(** Implementation of the [io] module BIFs.

    Supports io:format/2, io:format/1, io:write/1, io:nl/0, io:writeln/1.

    Format specifiers supported by io:format:
      ~w   write term in Erlang syntax (uses Value_printer.pp)
      ~p   pretty-print term (same as ~w here; no indentation)
      ~s   write a list of character codes as a string
      ~a   write atom name without surrounding quotes
      ~c   write next arg (integer) as a character
      ~b   write integer in base 10
      ~e   write number in scientific notation
      ~f   write number in fixed-point notation
      ~g   write number in shorter of ~e / ~f
      ~i   ignore (consume) next arg
      ~n   newline
      ~N   newline
      ~~   literal tilde
      ~Nr  write integer in base N (e.g. ~16r for hex, ~8r for octal)
      ~Nc  write fill character N times
      ~*c  use next arg as repeat count, then write fill character

    Reference: https://www.erlang.org/doc/man/io.html#format-1

    @author Yu-Yang Lin
 *)

open Ast

(* ------------------------------------------------------------------ *)
(* Helpers                                                              *)
(* ------------------------------------------------------------------ *)

let value_to_chars v =
  let rec go = function
    | V_nil                -> []
    | V_cons (V_int c, tl) -> Char.chr (Z.to_int c land 0xFF) :: go tl
    | V_cons (V_char c, tl) -> c :: go tl
    | _ -> failwith "io:format: format string must be a character list"
  in go v

let value_to_list v =
  let rec go = function
    | V_nil           -> []
    | V_cons (h, tl)  -> h :: go tl
    | _ -> failwith "io:format: argument list must be a proper list"
  in go v

(* ------------------------------------------------------------------ *)
(* String output for ~s                                                 *)
(* ------------------------------------------------------------------ *)

let write_string v =
  let rec go = function
    | V_nil                 -> ()
    | V_cons (V_int c, tl)  -> print_char (Char.chr (Z.to_int c land 0xFF)); go tl
    | V_cons (V_char c, tl) -> print_char c; go tl
    | _ -> failwith "io:format ~s: argument must be a character list"
  in go v

(* ------------------------------------------------------------------ *)
(* Integer base formatting for ~Nr                                      *)
(* ------------------------------------------------------------------ *)

let format_base v base =
  if base < 2 || base > 36 then
    failwith (Printf.sprintf "io:format ~r: base %d out of range (2..36)" base);
  let digits = "0123456789abcdefghijklmnopqrstuvwxyz" in
  let zbase = Z.of_int base in
  if Z.equal v Z.zero then "0"
  else
    let rec go n acc =
      if Z.equal n Z.zero then acc
      else go (Z.div n zbase) (String.make 1 digits.[Z.to_int (Z.rem n zbase)] ^ acc)
    in
    if Z.lt v Z.zero then "-" ^ go (Z.neg v) "" else go v ""

(* ------------------------------------------------------------------ *)
(* Format string processor                                              *)
(* ------------------------------------------------------------------ *)

let process_format fun_name fmt_chars arg_list =
  let consume args =
    match args with
    | []      -> failwith (Printf.sprintf
                             "io:%s: too few arguments for format string" fun_name)
    | x :: xs -> (x, xs)
  in
  let write v =
    Value_printer.pp Format.std_formatter v;
    Format.pp_print_flush Format.std_formatter ()
  in
  let rec go fmt args =
    match fmt with
    | []          -> ()
    | '~' :: rest -> spec rest args
    | c   :: rest -> print_char c; go rest args

  and spec fmt args =
    match fmt with
    | 'n' :: rest | 'N' :: rest -> print_char '\n';  go rest args
    | '~' :: rest               -> print_char '~';   go rest args
    | 'w' :: rest | 'p' :: rest ->
        let (arg, args') = consume args in write arg; go rest args'
    | 's' :: rest ->
        let (arg, args') = consume args in write_string arg; go rest args'
    | 'a' :: rest ->
        let (arg, args') = consume args in
        (match arg with V_atom a -> print_string a | _ -> write arg);
        go rest args'
    | 'c' :: rest ->
        let (arg, args') = consume args in
        (match arg with
         | V_int c -> print_char (Char.chr (Z.to_int c land 0xFF))
         | _ -> failwith "io:format ~c: argument must be an integer");
        go rest args'
    | 'b' :: rest ->
        let (arg, args') = consume args in
        (match arg with
         | V_int n -> print_string (Z.to_string n)
         | _ -> failwith "io:format ~b: argument must be an integer");
        go rest args'
    | 'e' :: rest | 'f' :: rest | 'g' :: rest ->
        let (arg, args') = consume args in
        (match arg with
         | V_float f -> print_string (Printf.sprintf "%g" f)
         | V_int n   -> print_string (Printf.sprintf "%g" (Z.to_float n))
         | _ -> failwith "io:format ~e/~f/~g: argument must be a number");
        go rest args'
    | 'i' :: rest ->
        let (_, args') = consume args in go rest args'
    | '*' :: rest ->
        let (arg, args') = consume args in
        let n = match arg with
          | V_int n -> Z.to_int n
          | _ -> failwith "io:format ~*: column argument must be an integer"
        in
        spec_num rest args' n
    | c :: rest when c >= '0' && c <= '9' ->
        spec_num rest args (Char.code c - Char.code '0')
    | c :: _ ->
        failwith (Printf.sprintf "io:format: unknown specifier '~%c'" c)
    | [] ->
        failwith "io:format: format string ends with bare '~'"

  and spec_num fmt args n =
    match fmt with
    | c :: rest when c >= '0' && c <= '9' ->
        spec_num rest args (n * 10 + Char.code c - Char.code '0')
    | 'r' :: rest ->
        let (arg, args') = consume args in
        (match arg with
         | V_int v -> print_string (format_base v n)
         | _ -> failwith "io:format ~r: argument must be an integer");
        go rest args'
    | 'c' :: rest ->
        let (arg, args') = consume args in
        (match arg with
         | V_int c ->
             for _ = 1 to n do print_char (Char.chr (Z.to_int c land 0xFF)) done
         | _ -> failwith "io:format ~Nc: argument must be a character code");
        go rest args'
    | c :: rest ->
        spec (c :: rest) args
    | [] ->
        failwith "io:format: format string ends after numeric prefix"
  in
  go fmt_chars arg_list

(* ------------------------------------------------------------------ *)
(* Dispatch                                                             *)
(* ------------------------------------------------------------------ *)

(** When [true], all io output is suppressed (functions still return ['ok']). *)
let suppress_io : bool ref = ref false

let dispatch (fun_name : string) (args : value list)
    (conf : process_conf) (rest : eval_cxt)
    : process_conf status =
  let ok () = return_val conf rest (V_atom "ok") in
  if !suppress_io then ok ()
  else
  match fun_name, args with
  | "format", [fmt_val; args_val]
  | "fwrite", [fmt_val; args_val] ->
      process_format fun_name (value_to_chars fmt_val) (value_to_list args_val);
      flush stdout; ok ()
  | "format", [fmt_val]
  | "fwrite", [fmt_val] ->
      process_format fun_name (value_to_chars fmt_val) [];
      flush stdout; ok ()
  | "write", [v] ->
      Value_printer.pp Format.std_formatter v;
      Format.pp_print_flush Format.std_formatter ();
      ok ()
  | "nl", [] ->
      print_char '\n'; flush stdout; ok ()
  | "writeln", [v] ->
      Value_printer.pp Format.std_formatter v;
      Format.pp_print_flush Format.std_formatter ();
      print_char '\n'; flush stdout; ok ()
  | "print", [v] ->
      Value_printer.pp Format.std_formatter v;
      Format.pp_print_flush Format.std_formatter ();
      print_char '\n'; flush stdout; ok ()
  | _ ->
      failwith (Printf.sprintf "[WIP] io:%s/%d not implemented"
                  fun_name (List.length args))
