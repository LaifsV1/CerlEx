(** Network-level execution trace: the sequence of events recorded along a
    scheduler path, plus its pretty-printer.  Pure data, factored out of
    [scheduler.ml] so that file holds only the exploration algorithm.  The
    scheduler's bound/deadlock/exception loggers stay in [scheduler.ml] because
    they touch scheduler globals; they call [pp_trace] here. *)

open Sexplib.Std
open Ast

(** One network-level event inside an [epoch]. *)
type trace_event =
  | Ev_send    of { src : pid; dst : pid; msg : value }
  | Ev_spawn   of { parent : pid; child : pid }
  | Ev_receive of { receiver : pid; src : pid; msg : value }
  | Ev_timeout of { receiver : pid }
  | Ev_ets     of { pid : pid; op : string; tid : int; arg : value option }
      (** ETS shared-state event: [op] is a short tag ("new", "insert",
          "lookup", "lookup_nil", "badarg", "delete", "owner_exit"), [arg]
          the object/key involved (if any).  Producer events land in
          [Commuting] epochs, scheduled observer decisions in [Scheduled]. *)
[@@deriving sexp_of]

(** A batch of network-level events from one round.
    [Commuting evs]: sends/spawns from [maximise] -- mutually independent, order irrelevant to equivalence.
    [Scheduled evs]: receive/timeout decisions from [schedule] -- the observable branching points. *)
type epoch =
  | Commuting of trace_event list
  | Scheduled of trace_event list
[@@deriving sexp_of]

(** Count [Scheduled] epochs; used for the [b2] bound. *)
let trace_length (t : epoch list) : int =
  List.fold_left
    (fun n ep -> match ep with Scheduled _ -> n + 1 | Commuting _ -> n)
    0 t

let pp_trace (t : epoch list) =
  Sexplib.Sexp.to_string_hum (sexp_of_list sexp_of_epoch t)

(** [trace_equiv t1 t2] decides whether two traces are equivalent.

    [TODO Layer 2]: this is a stub.  A correct implementation requires:
    - Proper structural value equality (polymorphic [=] fails on closures).
    - Pid alpha-renaming (pids from two different programs are not
    numerically comparable). *)
let trace_equiv (_t1 : epoch list) (_t2 : epoch list) : bool =
  failwith "[TODO] trace_equiv"
