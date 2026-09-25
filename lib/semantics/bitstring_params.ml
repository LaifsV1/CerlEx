(** Parsed Core Erlang bitstring segment parameters.

    This module is a PLACEHOLDER.

    TODO: This module checks only the shape of the evaluated parameter
    list. It does not try to enumerate every supported segment type or flag;
    the eventual bitstring encoder/matcher should decide which atoms and
    combinations it supports.

    Accepted layouts are the Core/OTP bitstring segment parameter layouts:
    - [Type; Flags]
    - [Size; Type; Flags]
    - [Size; Unit; Type; Flags]

    The parsed [typ] and [flags] fields preserve the atoms emitted by the
    compiler so that newly encountered parameters are reported by the encoder
    rather than hidden by this parser.
 *)

open Sexplib.Std
open Syntax.Core_ast
open Ast
open Utils.Result_syntax (* load let* monadic bind *)

type t = {
    size  : value;          (** Usually ['all'] or an integer value; interpreted by the encoder. *)
    unit  : int option;     (** Unit value; [None] = ['undefined'] (UTF types have no fixed unit). *)
    typ   : atom;           (** Segment type atom, e.g. ['integer'], ['binary'], ['utf8']. *)
    flags : atom list;      (** Segment flag atoms, e.g. ['signed'], ['big']. *)
  }
[@@deriving sexp_of]

let string_of_value (v : value) : string =
  Sexplib0.Sexp.to_string_hum (sexp_of_value v)

let string_of_values (vs : value list) : string =
  Sexplib0.Sexp.to_string_hum ([%sexp_of: value list] vs)

let expected (field : string) (kind : string) (v : value) : ('a, string) result =
  Error ("expected " ^ field ^ " to be " ^ kind ^ ", got: " ^ string_of_value v)

let int_opt_of_value (field : string) (v : value) : (int option, string) result =
  match v with
  | V_int n    -> Ok (Some (Z.to_int n))
  | V_atom "undefined" -> Ok None
  | _ -> expected field "an integer or 'undefined'" v

let atom_of_value (field : string) (v : value) : (atom, string) result =
  match v with
  | V_atom a -> Ok a
  | _ -> expected field "an atom" v

let rec proper_list_of_value (field : string) (v : value) : (value list, string) result =
  match v with
  | V_nil -> Ok []
  | V_cons (x, xs) ->
      let* tl = proper_list_of_value field xs in
      Ok (x :: tl)
  | _ -> expected field "a proper list" v

let atom_list_of_value (field : string) (v : value) : (atom list, string) result =
  let* xs = proper_list_of_value field v in
  let rec aux i acc = function
    | [] -> Ok (List.rev acc)
    | x :: xs ->
        let* a = atom_of_value (field ^ "[" ^ string_of_int i ^ "]") x in
        aux (i + 1) (a :: acc) xs
  in
  aux 0 [] xs

let make (size : value) (unit_v : value) (typ_v : value) (flags_v : value)
  : (t, string) result =
  let* unit = int_opt_of_value "bitstring unit" unit_v in
  let* typ = atom_of_value "bitstring type" typ_v in
  let* flags = atom_list_of_value "bitstring flags" flags_v in
  Ok { size; unit; typ; flags }

let of_value_list (vs : value list) : (t, string) result =
  match vs with
  | [typ; flags] ->
      make (V_atom "all") (V_int Z.one) typ flags
  | [size; typ; flags] ->
      make size (V_int Z.one) typ flags
  | [size; unit; typ; flags] ->
      make size unit typ flags
  | _ ->
      Error
        ("unexpected bitstring parameter arity: "
         ^ string_of_int (List.length vs)
         ^ "; got: "
         ^ string_of_values vs)
