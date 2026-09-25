(** Canonical string representation of a [network_conf] for memoisation.

    Flattens all runtime environments and values into integer IDs using global
    intern tables, breaking the env->closure->env recursion that made naive
    sexp serialisation impractical.  The resulting string is used as a key in
    the scheduler's bounded memo set to detect already-explored states.

    See [notes/canonicalisation.md] for a full description.

    @author Yu-Yang Lin
    @since 2026-05-29
 *)

open Syntax.Core_ast
open Ast

(* -------------------------------------------------------------------- *)
(* Global expr/clause sexp cache                                        *)
(*                                                                      *)
(* Parse-time AST nodes are fixed for the lifetime of the program, so   *)
(* we cache their sexp strings globally to avoid recomputing them.      *)
(* -------------------------------------------------------------------- *)

let expr_cache : (expr, string) Hashtbl.t = Hashtbl.create 128 (* why 128? modify if it's too small *)

let expr_str (e : expr) : string =
  match Hashtbl.find_opt expr_cache e with
  | Some s -> s
  | None ->
    let s = Sexplib.Sexp.to_string (sexp_of_expr e) in
    Hashtbl.add expr_cache e s; s

let sexp_list f xs = Sexplib.Sexp.to_string (Sexplib.Std.sexp_of_list f xs)

let clauses_str (cs : clause list)   : string = sexp_list sexp_of_clause cs
let segs_str    (ss : bitstring list): string = sexp_list sexp_of_bitstring ss
let exprs_str   (es : expr list)     : string = sexp_list sexp_of_expr es

(* -------------------------------------------------------------------- *)
(* Flat types                                                             *)
(* -------------------------------------------------------------------- *)

type value_id = int
type env_id   = int

(** flat value. complex values are an ID. *)
type flat_value =
  | FV_int   of string   (* Z.to_string n *)
  | FV_float of float
  | FV_char  of char
  | FV_atom  of string
  | FV_nil
  | FV_pid   of int
  | FV_ref   of int
  | FV_ets_tid of int
  | FV_id    of value_id

(** One-level-deep definition of a complex value stored in the value table.
    Sub-values are [flat_value]s: scalars inline, nested complex values as IDs. *)
type canonical_value =
  | VD_cons    of flat_value * flat_value
  | VD_tuple   of flat_value list
  | VD_closure of flat_closure
  | VD_binary  of string * int   (* hex string of bits, len_bits *)
  | VD_map     of (flat_value * flat_value) list  (* sorted key-value pairs *)

and flat_closure = {
  fc_vars : var_name list;
  fc_body : expr;            (* does not have run-time values, only parse-time literals *)
  fc_env  : env_id;
}

(** Flat environment: sorted association lists (from [VarMap.bindings] /
    [FnameMap.bindings]) so that structural [(=)] is correct regardless
    of insertion order. *)
type flat_env = {
  fe_vars : (var_name * flat_value) list;
  fe_funs : (fname * flat_closure) list;
}


(* -------------------------------------------------------------------- *)
(* Flat-type serializers                                                  *)
(* -------------------------------------------------------------------- *)

let si = string_of_int
let cat sep xs = String.concat sep xs

let fv_str : flat_value -> string = function
  | FV_int s   -> "i" ^ s
  | FV_float f -> "f" ^ string_of_float f
  | FV_char c  -> "c" ^ String.make 1 c
  | FV_atom a  -> "a\"" ^ String.escaped a ^ "\""
  | FV_nil     -> "n"
  | FV_pid p   -> "p" ^ si p
  | FV_ref r   -> "r" ^ si r
  | FV_ets_tid t -> "t" ^ si t
  | FV_id id   -> "@" ^ si id

let fc_str (fc : flat_closure) : string =
  cat "," fc.fc_vars ^ "|" ^ expr_str fc.fc_body ^ "|@" ^ si fc.fc_env

let cv_str : canonical_value -> string = function
  | VD_cons(h, t) -> "(" ^ fv_str h ^ "." ^ fv_str t ^ ")"
  | VD_tuple fvs  -> "[" ^ cat "," (List.map fv_str fvs) ^ "]"
  | VD_closure fc -> "{" ^ fc_str fc ^ "}"
  | VD_binary (hex, len) -> "<" ^ hex ^ ":" ^ si len ^ ">"
  | VD_map kvs    ->
      "M[" ^ cat "," (List.map (fun (k,v) -> fv_str k ^ "->" ^ fv_str v) kvs) ^ "]"

let fe_str (fe : flat_env) : string =
  let vs =
    fe.fe_vars
    |> List.map (fun (x, fv) -> x ^ "=" ^ fv_str fv)
    |> cat ","
  in
  let fs =
    fe.fe_funs
    |> List.map (fun (f, fc) ->
        f.fn_name ^ "/" ^ si f.fn_arity ^ "=[" ^ fc_str fc ^ "]")
    |> cat ","
  in
  vs ^ "|" ^ fs

(* -------------------------------------------------------------------- *)
(* Global intern tables                                                   *)
(* -------------------------------------------------------------------- *)

let vctr = ref 0
let ectr = ref 0
let vtable : (canonical_value, value_id) Hashtbl.t = Hashtbl.create 64
let etable : (flat_env, env_id) Hashtbl.t = Hashtbl.create 16

let alloc_v (cv : canonical_value) : value_id =
  match Hashtbl.find_opt vtable cv with
  | Some id -> id
  | None ->
    let id = !vctr in incr vctr;
    Hashtbl.add vtable cv id; id

let alloc_e (fe : flat_env) : env_id =
  match Hashtbl.find_opt etable fe with
  | Some id -> id
  | None ->
    let id = !ectr in incr ectr;
    Hashtbl.add etable fe id; id

(* Retained receive matchers on forced-order nodes: intern clause lists to
   integer ids (a clause list prints deterministically, but one printed copy
   per retained receive would bloat the string; identical lists share an
   id).  Keyed on the sexp string so equality matches the printed form. *)
let cctr = ref 0
let ctable : (string, int) Hashtbl.t = Hashtbl.create 16

let alloc_c (cs : clause list) : int =
  let s = clauses_str cs in
  match Hashtbl.find_opt ctable s with
  | Some id -> id
  | None ->
    let id = !cctr in incr cctr;
    Hashtbl.add ctable s id; id

(* -------------------------------------------------------------------- *)
(* Flattening functions                                                   *)
(* -------------------------------------------------------------------- *)

let rec flatten_value (v : value) : flat_value =
  match v with
  | V_int n      -> FV_int (Z.to_string n)
  | V_float f    -> FV_float f
  | V_char c     -> FV_char c
  | V_atom a     -> FV_atom a
  | V_ref r      -> FV_ref r
  | V_ets_tid t  -> FV_ets_tid t
  | V_nil        -> FV_nil
  | V_pid p      -> FV_pid p
  | V_cons(h, t) -> FV_id (alloc_v (VD_cons (flatten_value h, flatten_value t)))
  | V_tuple vs   -> FV_id (alloc_v (VD_tuple (List.map flatten_value vs)))
  | V_closure c  -> FV_id (alloc_v (VD_closure (flatten_closure c)))
  | V_binary (bits, len) -> FV_id (alloc_v (VD_binary (Z.format "%x" bits, len)))
  | V_map kvs ->
      FV_id (alloc_v (VD_map (List.map (fun (k,v) -> (flatten_value k, flatten_value v)) kvs)))

and flatten_closure (c : closure) : flat_closure =
  { fc_vars = c.clo_vars
  ; fc_body = c.clo_body
  ; fc_env  = intern_env c.clo_env }

and intern_env (env : env) : env_id =
  alloc_e (flatten_env env)

and flatten_env (env : env) : flat_env =
  { fe_vars = List.map (fun (x, v) -> (x, flatten_value v)) (VarMap.bindings env.vars)
  ; fe_funs = List.map (fun (f, c) -> (f, flatten_closure c)) (FnameMap.bindings env.funs) }

(* -------------------------------------------------------------------- *)
(* to_string                                                              *)
(* -------------------------------------------------------------------- *)

let to_string (nc : network_conf) : string =
  let nc = { nc with
    processes = List.sort (fun a b -> compare a.pid b.pid) nc.processes;
    next_pid  = 0 }
  in

  (* Flatten a value and immediately serialise it. *)
  let fv  v   = fv_str (flatten_value v) in
  (* Intern an environment and return the id as a string. *)
  let ei  env = si (intern_env env) in
  (* Flatten and serialise a list of values as comma-separated flat values. *)
  let fvs vs  = cat "," (List.map fv vs) in

  (* Serialise an inner_term: expressions stay as sexp strings, value
     sequences and raised exceptions use flat values. *)
  let ser_term : inner_term -> string = function
    | T_Expr e   -> "E" ^ expr_str e
    | T_Vals vs  -> "V[" ^ fvs vs ^ "]"
    | T_Raise ex ->
      let cls = match ex.class_ with
        | Error -> "error" | Exit -> "exit" | Throw -> "throw"
      in
      "R" ^ cls ^ "," ^ fv ex.reason ^ "," ^ fv ex.info
  in

  let acc_str (bits, len) = Z.format "%x" bits ^ ":" ^ si len in

  (* Serialise one CEK frame: values and environments become IDs,
     parse-time expressions stay as sexp strings. *)
  let ser_frame : eval_frame -> string = function
    | E_ValList (acc, es, rho) ->
      "VL[" ^ fvs acc ^ "|" ^ exprs_str es ^ "@" ^ ei rho ^ "]"
    | E_Tuple (acc, es, rho) ->
      "T[" ^ fvs acc ^ "|" ^ exprs_str es ^ "@" ^ ei rho ^ "]"
    | E_ConsHd (acc, es, tl, rho) ->
      "CH[" ^ fvs acc ^ "|" ^ exprs_str es ^ " " ^ expr_str tl ^ "@" ^ ei rho ^ "]"
    | E_ConsTl acc ->
      "CT[" ^ fvs acc ^ "]"
    | E_BitstrLhs (acc, rhs, segs, rho) ->
      "BL[" ^ acc_str acc ^ "|" ^ exprs_str rhs ^ " " ^ segs_str segs ^ "@" ^ ei rho ^ "]"
    | E_BitstrRhs (acc, lhs, rhs_acc, es, segs, rho) ->
      "BR[" ^ acc_str acc ^ " " ^ fv lhs ^ " [" ^ fvs rhs_acc ^ "]"
      ^ "|" ^ exprs_str es ^ " " ^ segs_str segs ^ "@" ^ ei rho ^ "]"
    | E_Let (xs, rhs, rho) ->
      "L[" ^ cat "," xs ^ " " ^ expr_str rhs ^ "@" ^ ei rho ^ "]"
    | E_Case (cls, rho) ->
      "C[" ^ clauses_str cls ^ "@" ^ ei rho ^ "]"
    | E_ApplyFun (es, rho) ->
      "AF[" ^ exprs_str es ^ "@" ^ ei rho ^ "]"
    | E_ApplyArgs (fn, acc, es, rho) ->
      "AA[" ^ fv fn ^ " " ^ fvs acc ^ "|" ^ exprs_str es ^ "@" ^ ei rho ^ "]"
    | E_QCallMod (me, args, rho) ->
      "QM[" ^ expr_str me ^ " " ^ exprs_str args ^ "@" ^ ei rho ^ "]"
    | E_QCallFun (mv, args, rho) ->
      "QF[" ^ fv mv ^ " " ^ exprs_str args ^ "@" ^ ei rho ^ "]"
    | E_QCallArgs (mv, fn, acc, es, rho) ->
      "QA[" ^ fv mv ^ " " ^ fv fn ^ " " ^ fvs acc ^ "|" ^ exprs_str es ^ "@" ^ ei rho ^ "]"
    | E_PrimOp (name, acc, es, rho) ->
      "PO[" ^ name ^ " " ^ fvs acc ^ "|" ^ exprs_str es ^ "@" ^ ei rho ^ "]"
    | E_Receive (cls, tb, rho) ->
      "RCV[" ^ clauses_str cls ^ " " ^ expr_str tb ^ "@" ^ ei rho ^ "]"
    | E_Try (vs, in_e, cvs, ce, rho) ->
      "TRY[" ^ cat "," vs ^ " " ^ expr_str in_e
      ^ " " ^ cat "," cvs ^ " " ^ expr_str ce ^ "@" ^ ei rho ^ "]"
    | E_Do (es, rho) ->
      "DO[" ^ exprs_str es ^ "@" ^ ei rho ^ "]"
    | E_Catch -> "catch"
    | E_MapKey (done_, op, ve, rest, base, rho) ->
      let op_s = match op with MapAssoc -> "=>" | MapExact -> ":=" in
      "MK[" ^ fvs (List.map (fun (_,k,_) -> k) done_)
      ^ "|" ^ op_s ^ " " ^ expr_str ve
      ^ " " ^ exprs_str (List.map (fun a -> a.ma_key) rest)
      ^ (match base with None -> "" | Some b -> "|" ^ expr_str b)
      ^ "@" ^ ei rho ^ "]"
    | E_MapVal (done_, k, op, rest, base, rho) ->
      let op_s = match op with MapAssoc -> "=>" | MapExact -> ":=" in
      "MV[" ^ fvs (List.map (fun (_,k2,_) -> k2) done_)
      ^ " " ^ fv k ^ " " ^ op_s
      ^ " " ^ exprs_str (List.map (fun a -> a.ma_key) rest)
      ^ (match base with None -> "" | Some b -> "|" ^ expr_str b)
      ^ "@" ^ ei rho ^ "]"
    | E_MapBase (pairs, rho) ->
      "MB[" ^ fvs (List.map (fun (_,k,_) -> k) pairs)
      ^ "@" ^ ei rho ^ "]"
    | E_Ets op ->
      let s = match op with
        | Ets_new    { tname; named }    -> "new " ^ tname ^ (if named then ";N" else "")
        | Ets_insert { tab; obj }        -> "ins " ^ fv tab ^ " " ^ fv obj
        | Ets_lookup { tab; key; elem }  ->
          "lkp " ^ fv tab ^ " " ^ fv key
          ^ (match elem with None -> "" | Some p -> ";" ^ si p)
        | Ets_delete { tab }             -> "del " ^ fv tab
      in
      "ETS[" ^ s ^ "]"
  in

  (* Serialise a commit clock as sorted pid:count pairs.  Clocks must be part
     of the canonical string: two states differing only in clocks can produce
     different branch sets (mailbox-order pruning reads the clocks), so they
     must not be merged by memoisation. *)
  let clock_str (c : clock) : string =
    cat "," (List.map (fun (p, n) -> si p ^ ":" ^ si n) (PidMap.bindings c))
  in

  let deferred_str = function
    | None -> ""
    | Some (Deferred_receive { srcs; timeout }) ->
      let srcs = List.sort compare srcs in
      let src_part = cat "," (List.map si srcs) in
      "R[" ^ src_part ^ (if timeout then ";T" else "") ^ "]"
    (* ETS deferral markers must be canonical for the same reason as R[...]:
       they restrict which branches a later round may offer. *)
    | Some Deferred_ets_write -> "RW[]"
    | Some (Deferred_ets_lookup { seen; nil_offered }) ->
      let seen = List.sort compare seen in
      "RL[" ^ cat "," (List.map (fun (p, n) -> si p ^ ":" ^ si n) seen)
      ^ (if nil_offered then ";N" else "") ^ "]"
  in

  (* Serialise one process: pid, env id, CEK term, frames, deferral, process dict, clock. *)
  let ser_proc (p : process_conf) : string =
    si p.pid ^ "@" ^ ei p.env
    ^ " " ^ ser_term p.cek.term
    ^ (match p.cek.ecxt with
       | []     -> ""
       | frames -> " " ^ cat " " (List.map ser_frame frames))
    ^ deferred_str p.deferred
    ^ (match p.pdict with
       | [] -> ""
       | kvs -> "D[" ^ cat "," (List.map (fun (k,v) -> fv k ^ "->" ^ fv v) kvs) ^ "]")
    ^ (if PidMap.is_empty p.clock then "" else "K{" ^ clock_str p.clock ^ "}")
  in

  (* Serialise one channel as dst<-src[flat messages].  Each message carries
     its send clock ('^{...}', omitted when empty) and, if flagged, its flag
     stamp ('!{...}' prefix). *)
  let ser_chan dst src (c : channel) : string =
    let ser_msg msg =
      (match msg.same_sender_visible with
       | None    -> ""
       | Some fc -> "!{" ^ clock_str fc ^ "}")
      ^ fv msg.value
      ^ (if PidMap.is_empty msg.send_clock then "" else "^{" ^ clock_str msg.send_clock ^ "}")
    in
    si dst ^ "<-" ^ si src ^ "[" ^ cat "," (List.map ser_msg c.msgs) ^ "]"
  in

  let procs_s = cat "|" (List.map ser_proc nc.processes) in
  let chans_s =
    PidMap.bindings nc.channels
    |> List.concat_map (fun (dst, inner) ->
        PidMap.bindings inner
        |> List.map (fun (src, c) -> ser_chan dst src c))
    |> cat " "
  in
  let refs_s =
    let order_s =
      List.sort compare nc.refs.order
      |> List.map (fun (a, b) -> si a ^ "<" ^ si b)
      |> cat ","
    in
    (* Stamps must be part of the canonical string: they are historical (a
       ref's creation clock), not derivable from the current state, and two
       states with the same live refs but different creation stamps can resolve
       a future ref comparison differently. *)
    let stamps_s =
      List.sort (fun (i, _) (j, _) -> compare i j) nc.refs.stamps
      |> List.map (fun (id, (creator, c)) -> si id ^ "@" ^ si creator ^ ":" ^ clock_str c)
      |> cat ","
    in
    order_s ^ (if stamps_s = "" then "" else "|" ^ stamps_s)
  in
  (* ETS state.  Tables, tombstone clocks, write events (with clocks) and name
     bindings are all behavioural: lookups/inserts branch on them, so two
     states differing in any of these must not be merged.  Tid values
     serialise as t<id> (a distinct kind from r<id> refs); their ids share the
     ref id space and their creation stamps live in the R[...|stamps] segment
     above.  (The observation-stamp clocks [observed_at]/[nil_observed_at]
     were part of this segment until 2026-07-25; they were retired with the
     mechanism that read them -- `notes/forced_order_handover.md` R1 -- so the
     ETS segment no longer carries an "@{...}" per write or an "N[...]" per
     table.  Two states that differ only in who had read a value now merge,
     which is correct: nothing branches on that any more.) *)
  let ets_s =
    if nc.ets.tables = [] then ""
    else
      let ser_write w =
        fv w.obj
        ^ (if PidMap.is_empty w.wclock then "" else "^{" ^ clock_str w.wclock ^ "}")
      in
      let ser_table t =
        si t.tid ^ "@" ^ si t.et_owner
        ^ (match t.et_name with None -> "" | Some n -> "(" ^ String.escaped n ^ ")")
        ^ (match t.dead with None -> "" | Some c -> "+{" ^ clock_str c ^ "}")
        ^ "{"
        ^ (t.writes
           |> List.sort (fun ((k1, p1), _) ((k2, p2), _) ->
                let c = Term_order.erlang_compare k1 k2 in
                if c <> 0 then c else compare p1 p2)
           |> List.map (fun ((k, p), ws) ->
                fv k ^ "," ^ si p ^ ":[" ^ cat "," (List.map ser_write ws) ^ "]")
           |> cat " ")
        ^ "}"
      in
      let tables_s =
        nc.ets.tables
        |> List.sort (fun a b -> compare a.tid b.tid)
        |> List.map ser_table
        |> cat "|"
      in
      "E[" ^ tables_s ^ "]"
  in
  (* Forced-order event store (notes/forced_order_graph_plan.md §6): nodes
     with kind, rf source and commit clock, sorted by node.  Stored edges are
     omitted -- they are a deterministic saturation of the events and their
     clocks, so serialising them would be redundant.  The node clocks must be
     part of the string for the same reason as ref creation stamps: they are
     historical (the commit-time clock, not recoverable from the current
     process clocks) and reachability reads them, so two states differing
     only in a node clock can prune differently. *)
  let fo_s =
    if PidMap.is_empty nc.fo.fo_events then ""
    else
      let node_s (p, t) = si p ^ ":" ^ si t in
      let ser_ev n (ev, c) =
        node_s n ^ "=" ^
        (match ev with
         | Fo_write { fo_tid; fo_key } ->
           "w(" ^ si fo_tid ^ "," ^ fv fo_key ^ ")"
         | Fo_read { fo_tid; fo_key; fo_from } ->
           "r(" ^ si fo_tid ^ "," ^ fv fo_key ^ ","
           ^ (match fo_from with None -> "-" | Some m -> node_s m) ^ ")"
         | Fo_send { fo_dst } ->
           "s(" ^ si fo_dst ^ ")"
         | Fo_recv { fo_dst; fo_consumed; fo_clauses; fo_env } ->
           "c(" ^ si fo_dst ^ "," ^ node_s fo_consumed ^ ","
           ^ si (alloc_c fo_clauses) ^ "," ^ ei fo_env ^ ")")
        ^ (if PidMap.is_empty c then "" else "^{" ^ clock_str c ^ "}")
      in
      (* Nested folds visit keys ascending, so prepending yields the
         node-descending list; the final rev restores node order.  No sort
         needed, and everything is tail-recursive (the store grows with
         path length). *)
      let entries =
        PidMap.fold (fun p ts acc ->
          TickMap.fold (fun t evc acc -> ser_ev (p, t) evc :: acc) ts acc
        ) nc.fo.fo_events [] in
      "F[" ^ cat "|" (List.rev entries) ^ "]"
  in
  "P[" ^ procs_s ^ "]C[" ^ chans_s ^ "]R[" ^ refs_s ^ "]" ^ ets_s ^ fo_s
