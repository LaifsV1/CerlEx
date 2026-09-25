(** Format-based pretty-printer for runtime [Ast.value] terms.

    Prints values in Erlang term syntax, suitable for both the [cerlex -i]
    output line and the [~w] / [~p] format specifiers in [Io_bifs].

    @author Yu-Yang Lin
 *)

open Ast

(* Atom quoting rules matching Erlang's ~w: quote if empty, reserved word,
   first char not [a-z], or any char not in [a-zA-Z0-9_@]. *)
let erlang_reserved_words = [
  "after"; "and"; "andalso"; "band"; "begin"; "bnot"; "bor"; "bsl";
  "bsr"; "bxor"; "case"; "catch"; "cond"; "div"; "end"; "fun"; "if";
  "let"; "not"; "of"; "or"; "orelse"; "query"; "receive"; "rem";
  "try"; "when"; "xor"
]

let atom_needs_quotes s =
  if s = "" then true
  else if List.mem s erlang_reserved_words then true
  else
    let is_atom_char c =
      (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
      (c >= '0' && c <= '9') || c = '_' || c = '@'
    in
    let n = String.length s in
    not (s.[0] >= 'a' && s.[0] <= 'z') ||
    (let rec check i =
       if i >= n then false else not (is_atom_char s.[i]) || check (i + 1)
     in check 1)

let pp_atom fmt s =
  if atom_needs_quotes s then Format.fprintf fmt "'%s'" s
  else Format.pp_print_string fmt s

let rec pp fmt v =
  match v with
  | V_int n     -> Format.pp_print_string fmt (Z.to_string n)
  | V_float f   -> Format.fprintf fmt "%.17g" f
  | V_char c    -> Format.fprintf fmt "$%c" c
  | V_atom a    -> pp_atom fmt a
  | V_ref r     -> Format.fprintf fmt "#Ref<%d>" r
  | V_ets_tid t -> Format.fprintf fmt "#Tab<%d>" t
  | V_nil       -> Format.pp_print_string fmt "[]"
  | V_pid p     -> Format.fprintf fmt "#pid<%d>" p
  | V_closure _ -> Format.pp_print_string fmt "#fun"
  | V_binary (bits, len_bits) ->
      (* Prints <<b0,b1,...,bN>> for byte-aligned binaries and
         <<b0,...,bN,last:rem>> for non-byte-aligned ones, where b0 is the
         most significant byte and last is the low rem_bits partial byte.
         Z.extract bits pos len extracts [len] bits at LSB-offset [pos]. *)
      let n_bytes  = len_bits / 8 in
      let rem_bits = len_bits mod 8 in
      Format.pp_print_string fmt "<<";
      for i = 0 to n_bytes - 1 do
        if i > 0 then Format.pp_print_char fmt ',';
        Format.pp_print_int fmt
          (Z.to_int (Z.extract bits ((n_bytes - 1 - i) * 8 + rem_bits) 8))
      done;
      if rem_bits > 0 then begin
        if n_bytes > 0 then Format.pp_print_char fmt ',';
        Format.fprintf fmt "%d:%d" (Z.to_int (Z.extract bits 0 rem_bits)) rem_bits
      end;
      Format.pp_print_string fmt ">>"
  | V_tuple vs  ->
      let pp_sep fmt () = Format.pp_print_char fmt ',' in
      Format.fprintf fmt "{%a}" (Format.pp_print_list ~pp_sep pp) vs
  | V_map []  -> Format.pp_print_string fmt "#{}"
  | V_map kvs ->
      let pp_sep fmt () = Format.pp_print_char fmt ',' in
      let pp_kv fmt (k, v) = Format.fprintf fmt "%a=>%a" pp k pp v in
      Format.fprintf fmt "#{%a}" (Format.pp_print_list ~pp_sep pp_kv) kvs
  | V_cons _ as v -> pp_cons fmt v

and pp_cons fmt v =
  let rec rest fmt = function
    | V_nil        -> ()
    | V_cons (h, t) ->
        Format.pp_print_char fmt ',';
        pp fmt h;
        rest fmt t
    | tail ->
        Format.pp_print_char fmt '|';
        pp fmt tail
  in
  match v with
  | V_cons (h, t) ->
      Format.pp_print_char fmt '[';
      pp fmt h;
      rest fmt t;
      Format.pp_print_char fmt ']'
  | _ -> pp fmt v

let pp_exception fmt (ex : raised_exception) =
  let cls = match ex.class_ with
    | Error -> "error" | Exit -> "exit" | Throw -> "throw"
  in
  Format.fprintf fmt "%s:%a (info: %a)" cls pp ex.reason pp ex.info
