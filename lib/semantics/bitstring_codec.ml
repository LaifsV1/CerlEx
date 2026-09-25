(** Bitstring encoding and decoding for the CerlEx CEK machine.

    All bit-level operations use [Z.t] (Zarith) as the bit buffer.  A
    bitstring is represented as [(bits, len_bits)] where [bits] is the
    integer value of the bitstring read MSB-first (big-endian natural
    order) and [len_bits] is the total bit count.

    Concatenation: [(a << b_len) | b].
    Top-N extraction: [bits >> (len - N)], masked to N bits.

    @author Yu-Yang Lin
    @since 2026-06-05
 *)

open Ast

(* -------------------------------------------------------------------- *)
(* Primitive bit operations                                               *)
(* -------------------------------------------------------------------- *)

let bits_concat (a, a_len) (b, b_len) =
  (Z.logor (Z.shift_left a b_len) b, a_len + b_len)

let bits_extract_top (bits, len) n =
  if n > len then
    failwith (Printf.sprintf "[bitstring_codec] extract: need %d bits but only %d remain" n len);
  let seg  = Z.shift_right bits (len - n) in
  let mask = Z.pred (Z.shift_left Z.one (len - n)) in
  let rem  = Z.logand bits mask in
  (seg, (rem, len - n))

(* Reverse byte order of an [n_bits]-wide integer (n_bits must be a multiple of 8). *)
let reverse_bytes bits n_bits =
  let n_bytes = n_bits / 8 in
  let rec loop acc b i =
    if i = 0 then acc
    else
      let byte = Z.logand b (Z.of_int 0xFF) in
      loop (Z.logor (Z.shift_left acc 8) byte) (Z.shift_right_trunc b 8) (i - 1)
  in
  loop Z.zero bits n_bytes

(* Mask [v] to its low [n] bits (two's-complement representation for negative [Z.t]). *)
let mask_to n v = Z.logand v (Z.pred (Z.shift_left Z.one n))

(* -------------------------------------------------------------------- *)
(* UTF encoding                                                           *)
(* -------------------------------------------------------------------- *)

let encode_utf8 cp =
  if cp < 0 || cp > 0x10FFFF then
    failwith (Printf.sprintf "[bitstring_codec] utf8: invalid codepoint %d" cp);
  if cp <= 0x7F then
    (Z.of_int cp, 8)
  else if cp <= 0x7FF then
    let b0 = 0xC0 lor (cp lsr 6) in
    let b1 = 0x80 lor (cp land 0x3F) in
    (Z.of_int ((b0 lsl 8) lor b1), 16)
  else if cp <= 0xFFFF then
    let b0 = 0xE0 lor (cp lsr 12) in
    let b1 = 0x80 lor ((cp lsr 6) land 0x3F) in
    let b2 = 0x80 lor (cp land 0x3F) in
    (Z.of_int ((b0 lsl 16) lor (b1 lsl 8) lor b2), 24)
  else
    let b0 = 0xF0 lor (cp lsr 18) in
    let b1 = 0x80 lor ((cp lsr 12) land 0x3F) in
    let b2 = 0x80 lor ((cp lsr 6) land 0x3F) in
    let b3 = 0x80 lor (cp land 0x3F) in
    (Z.of_int ((b0 lsl 24) lor (b1 lsl 16) lor (b2 lsl 8) lor b3), 32)

let encode_utf16 cp little =
  if cp <= 0xFFFF then
    let raw  = Z.of_int cp in
    let bits = if little then reverse_bytes raw 16 else raw in
    (bits, 16)
  else begin
    let cp'  = cp - 0x10000 in
    let hi   = 0xD800 lor (cp' lsr 10) in
    let lo   = 0xDC00 lor (cp' land 0x3FF) in
    let raw  = Z.of_int ((hi lsl 16) lor lo) in
    let bits = if little then reverse_bytes raw 32 else raw in
    (bits, 32)
  end

(* -------------------------------------------------------------------- *)
(* UTF decoding                                                           *)
(* -------------------------------------------------------------------- *)

let decode_utf8 (bits, len) =
  if len < 8 then None
  else
    let byte0 = Z.to_int (Z.shift_right bits (len - 8)) land 0xFF in
    if byte0 land 0x80 = 0 then
      let (_seg, rem) = bits_extract_top (bits, len) 8 in
      Some (V_int (Z.of_int byte0), rem)
    else if byte0 land 0xE0 = 0xC0 then begin
      if len < 16 then None
      else
        let (w, rem) = bits_extract_top (bits, len) 16 in
        let b0 = Z.to_int (Z.shift_right w 8) land 0xFF in
        let b1 = Z.to_int w land 0xFF in
        let cp = ((b0 land 0x1F) lsl 6) lor (b1 land 0x3F) in
        Some (V_int (Z.of_int cp), rem)
    end
    else if byte0 land 0xF0 = 0xE0 then begin
      if len < 24 then None
      else
        let (w, rem) = bits_extract_top (bits, len) 24 in
        let b0 = Z.to_int (Z.shift_right w 16) land 0xFF in
        let b1 = Z.to_int (Z.shift_right w 8)  land 0xFF in
        let b2 = Z.to_int w land 0xFF in
        let cp = ((b0 land 0x0F) lsl 12) lor ((b1 land 0x3F) lsl 6) lor (b2 land 0x3F) in
        Some (V_int (Z.of_int cp), rem)
    end
    else if byte0 land 0xF8 = 0xF0 then begin
      if len < 32 then None
      else
        let (w, rem) = bits_extract_top (bits, len) 32 in
        let b0 = Z.to_int (Z.shift_right w 24) land 0xFF in
        let b1 = Z.to_int (Z.shift_right w 16) land 0xFF in
        let b2 = Z.to_int (Z.shift_right w 8)  land 0xFF in
        let b3 = Z.to_int w land 0xFF in
        let cp = ((b0 land 0x07) lsl 18) lor ((b1 land 0x3F) lsl 12)
                 lor ((b2 land 0x3F) lsl 6) lor (b3 land 0x3F) in
        Some (V_int (Z.of_int cp), rem)
    end
    else None

let decode_utf16 (bits, len) little =
  if len < 16 then None
  else
    let (raw16, rem) = bits_extract_top (bits, len) 16 in
    let raw16 = if little then reverse_bytes raw16 16 else raw16 in
    let hi = Z.to_int raw16 in
    if hi land 0xFC00 = 0xD800 then begin
      if snd rem < 16 then None
      else
        let (raw_lo, rem2) = bits_extract_top rem 16 in
        let raw_lo = if little then reverse_bytes raw_lo 16 else raw_lo in
        let lo = Z.to_int raw_lo in
        if lo land 0xFC00 <> 0xDC00 then None
        else
          let cp = 0x10000 + ((hi land 0x3FF) lsl 10) lor (lo land 0x3FF) in
          Some (V_int (Z.of_int cp), rem2)
    end
    else
      Some (V_int (Z.of_int hi), rem)

let decode_utf32 (bits, len) little =
  if len < 32 then None
  else
    let (raw, rem) = bits_extract_top (bits, len) 32 in
    let raw = if little then reverse_bytes raw 32 else raw in
    Some (V_int raw, rem)

(* -------------------------------------------------------------------- *)
(* Helpers                                                                *)
(* -------------------------------------------------------------------- *)

let is_little flags = List.mem "little" flags
let is_signed flags = List.mem "signed" flags

let codepoint_of_value v =
  match v with
  | V_int n  -> Z.to_int n
  | V_char c -> Char.code c
  | _ -> failwith "[bitstring_codec] UTF segment: value must be integer or char"

(* -------------------------------------------------------------------- *)
(* Encoding: construct a bitstring segment from a value and params       *)
(* -------------------------------------------------------------------- *)

(** [encode_segment acc lhs params] encodes [lhs] according to [params] and
    concatenates the result onto [acc].  Raises [Failure] on type errors. *)
let encode_segment acc (lhs : value) (params : Bitstring_params.t) =
  let little = is_little params.flags in
  match params.typ with
  | "integer" ->
      let unit_ = Option.value params.unit ~default:1 in
      let n_bits = match params.size with
        | V_int s -> Z.to_int s * unit_
        | _ -> failwith "[bitstring_codec] integer segment: size must be an integer" in
      let raw = match lhs with
        | V_int v  -> mask_to n_bits v
        | V_char c -> mask_to n_bits (Z.of_int (Char.code c))
        | _ -> failwith "[bitstring_codec] integer segment: value must be integer or char" in
      let bits = if little then reverse_bytes raw n_bits else raw in
      bits_concat acc (bits, n_bits)
  | "binary" ->
      let (src_bits, src_len) = match lhs with
        | V_binary (b, l) -> (b, l)
        | _ -> failwith "[bitstring_codec] binary segment: value must be a binary" in
      let unit_ = Option.value params.unit ~default:8 in
      let n_bits = match params.size with
        | V_atom "all" -> src_len
        | V_int s -> Z.to_int s * unit_
        | _ -> failwith "[bitstring_codec] binary segment: invalid size" in
      if n_bits > src_len then
        failwith "[bitstring_codec] binary segment: not enough bits in source";
      let (seg, _) = bits_extract_top (src_bits, src_len) n_bits in
      bits_concat acc (seg, n_bits)
  | "utf8" ->
      bits_concat acc (encode_utf8 (codepoint_of_value lhs))
  | "utf16" ->
      bits_concat acc (encode_utf16 (codepoint_of_value lhs) little)
  | "utf32" ->
      let cp  = codepoint_of_value lhs in
      let raw = Z.of_int cp in
      let bits = if little then reverse_bytes raw 32 else raw in
      bits_concat acc (bits, 32)
  | t -> failwith (Printf.sprintf "[bitstring_codec] unknown segment type: %s" t)

(* -------------------------------------------------------------------- *)
(* Decoding: extract one segment from a bitstring buffer                 *)
(* -------------------------------------------------------------------- *)

(** [decode_segment buf params] extracts one segment from the front of
    [buf] according to [params].  Returns [Some (value, remaining)] on
    success, [None] if the buffer does not contain enough bits.
    Raises [Failure] on bad parameters. *)
let decode_segment (buf : Z.t * int) (params : Bitstring_params.t)
    : (value * (Z.t * int)) option =
  let little = is_little params.flags in
  let signed = is_signed params.flags in
  let (bits, len) = buf in
  match params.typ with
  | "integer" ->
      let unit_ = Option.value params.unit ~default:1 in
      let n_bits = match params.size with
        | V_int s -> Z.to_int s * unit_
        | _ -> failwith "[bitstring_codec] integer pattern: size must be an integer" in
      if n_bits = 0 then
        Some (V_int Z.zero, buf)
      else if n_bits > len then None
      else
        let (seg, rem) = bits_extract_top (bits, len) n_bits in
        let seg = if little then reverse_bytes seg n_bits else seg in
        let value =
          if signed && Z.testbit seg (n_bits - 1) then
            Z.sub seg (Z.shift_left Z.one n_bits)
          else seg
        in
        Some (V_int value, rem)
  | "binary" ->
      let unit_ = Option.value params.unit ~default:8 in
      let n_bits = match params.size with
        | V_atom "all" -> len
        | V_int s -> Z.to_int s * unit_
        | _ -> failwith "[bitstring_codec] binary pattern: invalid size" in
      if n_bits > len then None
      else
        let (seg, rem) = bits_extract_top (bits, len) n_bits in
        Some (V_binary (seg, n_bits), rem)
  | "utf8"  -> decode_utf8  (bits, len)
  | "utf16" -> decode_utf16 (bits, len) little
  | "utf32" -> decode_utf32 (bits, len) little
  | t -> failwith (Printf.sprintf "[bitstring_codec] unknown segment type in pattern: %s" t)
