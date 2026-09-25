(** cerlex -- Core Erlang tool.

    Default mode (positional argument): parse a .core file and pretty-print it.
    Eval mode (-i <file>): parse a .core file, install all module functions via
    a top-level letrec, call main/0, and run focus/reduce until Done or Stuck.
    Explore mode (-e <file>): temporary hook for testing the Layer 1 scheduler.
    Parses and normalises a .core file, constructs a single-process
    [scheduler_conf], and calls [Semantics.Scheduler.explore].

    TODO: [-e] is a temporary hook for validating Layer 1 before proper
    migration.  Once Layer 1 is stable, [-i] should be replaced: the binary
    should always run via [explore] rather than [Reductions.run] directly,
    and this flag should be removed.

    @author Yu-Yang Lin
 *)

open Syntax.Core_ast

(* ------------------------------------------------------------------ *)
(* Command-line                                                         *)
(* ------------------------------------------------------------------ *)

let input_files  = ref []
let eval_mode    = ref false
let explore_mode = ref false

type entry_spec = {
  entry_module : string option;
  entry_fname  : fname;
}

let entry_point = ref None

let def_msg msg v = Printf.sprintf " %s\n      (default: %d)" msg v

let parse_entry s =
  let bad () =
    Printf.eprintf "cerlex: invalid -entry '%s' (expected [module:]name[/0])\n" s;
    exit 2
  in
  let parse_fname text =
    match String.split_on_char '/' text with
    | [name] when name <> "" -> { fn_name = name; fn_arity = 0 }
    | [name; "0"] when name <> "" -> { fn_name = name; fn_arity = 0 }
    | [_; _] ->
        Printf.eprintf "cerlex: entry arity must be 0: '%s'\n" s;
        exit 2
    | _ -> bad ()
  in
  match String.split_on_char ':' s with
  | [fname] ->
      { entry_module = None; entry_fname = parse_fname fname }
  | [mod_name; fname] when mod_name <> "" ->
      { entry_module = Some mod_name; entry_fname = parse_fname fname }
  | _ -> bad ()

let speclist = [
  ("-i", Arg.String (fun f -> eval_mode := true; input_files := f :: !input_files),
   "<root.core>  evaluate entry point until done or stuck (root module = first file)");
  ("-e", Arg.String (fun f -> explore_mode := true; input_files := f :: !input_files),
   "<root.core>  explore via the Layer 1 scheduler; temporary hook (root module = first file)");
  ("-entry", Arg.String (fun s -> entry_point := Some (parse_entry s)),
   "<[module:]name[/0]>  entry function (default: main/0 in the root module)");
  ("-b0", Arg.Set_int Semantics.Scheduler.b0,
   def_msg "<n>  max CEK steps per maximise round" !Semantics.Scheduler.b0);
  ("-b1", Arg.Set_int Semantics.Scheduler.b1,
   def_msg "<n>  max send/spawn resolutions per round" !Semantics.Scheduler.b1);
  ("-b2", Arg.Set_int Semantics.Scheduler.b2,
   def_msg "<n>  max scheduled epochs / trace depth" !Semantics.Scheduler.b2);
  ("-memo", Arg.Set_int Semantics.Scheduler.memo_size,
   def_msg "<n>  memoisation set capacity; 0 = disabled" !Semantics.Scheduler.memo_size);
  ("-bfs", Arg.Unit (fun () -> Semantics.Frontier.search_order := Semantics.Frontier.BFS),
   "  use breadth-first search instead of the default depth-first (BFS can grow the frontier to GBs)");
  ("-no-sleep", Arg.Clear Semantics.Scheduler.sleep_set,
   " disable the sleep set (eager Waiting-branch exploration; see notes/sleep_set_plan.md)");
  ("-no-fo", Arg.Clear Semantics.Forced_order.enabled,
   "  disable the forced-order graph: no branch vector is rejected for joint inconsistency, restoring pre-graph behaviour.  UNLIKE the other switches this CHANGES THE ANSWER -- reported counts are explicitly over-approximating (for A/B measurement; see notes/forced_order_handover.md)");
  ("-no-gc", Arg.Clear Semantics.Scheduler.gc,
   "  disable GC of unwakeable parked confs (on by default; memory only, counts unchanged; see notes/parked_conf_gc_plan.md)");
  ("-gc-refcount", Arg.Set Semantics.Scheduler.gc_refcount,
   "  use the incremental refcount GC instead of the batch sweep (same result; experimental)");
  ("-print-canon", Arg.Set Semantics.Scheduler.print_canon,
   "  print the canonical string of each network state to stderr");
  ("-prefix-stats", Arg.Set Semantics.Scheduler.prefix_stats,
   "  build the scheduler computation tree and report same-tree stateless replay and failed-speculation counts");
  ("-quiet", Arg.Tuple [Arg.Clear Semantics.Scheduler.verbose;
                        Arg.Clear Semantics.Erlang_bifs.verbose],
   "  suppress per-trace warnings and bound messages on stderr");
  ("-no-io", Arg.Set Semantics.Io_bifs.suppress_io,
   "  suppress all io:format/write/nl and erlang:display output (functions still return 'ok'/'true')");
]

let usage_msg =
  "usage: cerlex [-i <root.core> | -e <root.core>] [<extra.core> ...] [-entry [module:]name[/0]]\n" ^
  "  The first file is the root module; main/0 in that module is the default entry point.\n" ^
  "  Extra files (stdlib, helpers) are passed as positional arguments after the root."

let () =
  Arg.parse speclist
    (fun f -> input_files := f :: !input_files)
    usage_msg

let input_files () =
  match List.rev !input_files with
  | [] -> Arg.usage speclist usage_msg; exit 2
  | files -> files

let parse_file file =
  match Syntax.Core_parse.from_file file with
  | Ok m -> m
  | Error (`Parser_error msg) -> prerr_endline msg; exit 1

let parse_files () =
  List.map parse_file (input_files ())

let normalised_modules () =
  List.map Core_normalise.Recv_normalise.normalise_module (parse_files ())

let build_module_def (m : t) =
  let open Semantics.Ast in
  List.fold_left (fun acc fd ->
      let fe = fd.fd_body in
      let clo = {
        clo_vars = fe.fe_vars;
        clo_body = Expr_letrec { lrb_lhs = m.m_defs; lrb_rhs = fe.fe_body };
        clo_env  = Semantics.Reductions.empty_env;
      } in
      FnameMap.add fd.fd_name clo acc)
    FnameMap.empty m.m_defs

let build_module_table modules =
  List.fold_left (fun mt m ->
      Semantics.Call_dispatch.add_module m.m_name
        (build_module_def m) mt)
    Semantics.Call_dispatch.empty_module_table modules

let find_module modules name =
  List.find_opt (fun m -> m.m_name = name) modules

let select_entry modules =
  match modules with
  | [] -> assert false
  | root :: _ ->
      let spec =
        match !entry_point with
        | Some spec -> spec
        | None ->
            { entry_module = None;
              entry_fname = { fn_name = "main"; fn_arity = 0 } }
      in
      let module_name =
        match spec.entry_module with
        | Some name -> name
        | None -> root.m_name
      in
      match find_module modules module_name with
      | None ->
          Printf.eprintf "cerlex: entry module '%s' was not loaded\n" module_name;
          exit 1
      | Some m ->
          if not (List.mem spec.entry_fname m.m_fnames) then begin
            Printf.eprintf "cerlex: module '%s' does not export %s/%d"
              module_name spec.entry_fname.fn_name spec.entry_fname.fn_arity;
            if !entry_point = None then
              Printf.eprintf "; pass -entry [module:]name[/0] to select an exported entry point";
            Printf.eprintf "\n";
            exit 1
          end;
          module_name, spec.entry_fname

let entry_expr module_name fname =
  Expr_qualified_call {
    qc_mod = Expr_literal (Lit_atom module_name);
    qc_fun = Expr_literal (Lit_atom fname.fn_name);
    qc_args = [];
  }

(* ------------------------------------------------------------------ *)
(* Parse-and-print mode (default)                                      *)
(* ------------------------------------------------------------------ *)

let do_parse () =
  let modules = parse_files () in
  List.iter (fun m ->
      Format.printf "Parsed successfully: %s@.@." m.m_filename;
      Format.printf "%a@." (fun fmt x -> Syntax.Core_printer.pp fmt x) m)
    modules

let pp_value     = Semantics.Value_printer.pp
let pp_exception = Semantics.Value_printer.pp_exception

(* ------------------------------------------------------------------ *)
(* Evaluation mode (-i)                                                 *)
(* ------------------------------------------------------------------ *)

(** Install all module-level function definitions as closures using the
    letrec wrap trick, then call main/0.

    Wrapping in Expr_letrec reuses the exact letrec reduction rule from
    reductions.ml.  Each closure's body is itself a letrec over the whole
    module group, so the group is re-installed on every application and
    mutual recursion works at any call depth. *)
let do_eval () =
  let modules = normalised_modules () in
  let module_name, entry_fname = select_entry modules in
  let entry = entry_expr module_name entry_fname in
  let open Semantics.Ast in
  let mt = build_module_table modules in
  let conf = {
    pid          = 0;
    cek          = { ecxt = []; term = T_Expr entry };
    env          = Semantics.Reductions.empty_env;
    deferred     = None;
    pdict        = [];
    clock        = PidMap.empty;
  } in
  let print_conf_result (c' : process_conf) =
    match c'.cek.term with
    | T_Vals vs ->
        let pp_sep fmt () = Format.pp_print_string fmt ", " in
        Format.printf "Done: %a@."
          (Format.pp_print_list ~pp_sep pp_value) vs
    | T_Raise ex ->
        Format.printf "Core program terminated with uncaught exception: %a@." pp_exception ex
    | T_Expr _ ->
        Printf.eprintf "[cerlex] Done with T_Expr (internal error)\n";
        exit 1
  in
  (try
     let r = Semantics.Reductions.run mt conf in
     List.iter print_conf_result r.Semantics.Reductions.done_confs;
     List.iter (fun _ -> Format.printf "Stuck: process waiting on network action@.")
       r.Semantics.Reductions.stuck_confs
   with Failure msg ->
     Printf.eprintf "Evaluation error: %s\n" msg; exit 1)

(* ------------------------------------------------------------------ *)
(* Explore mode (-e)  [temporary Layer 1 hook]                         *)
(* ------------------------------------------------------------------ *)

let do_explore () =
  let modules = normalised_modules () in
  let module_name, entry_fname = select_entry modules in
  let entry = entry_expr module_name entry_fname in
  let open Semantics.Ast in
  let mt = build_module_table modules in
  let conf = {
    pid          = 0;
    cek          = { ecxt = []; term = T_Expr entry };
    env          = Semantics.Reductions.empty_env;
    deferred     = None;
    pdict        = [];
    clock        = PidMap.empty;
  } in
  let sc = Semantics.Scheduler.{
    network        = { processes = [conf]; channels = PidMap.empty; next_pid = 1
                     ; refs = empty_ref_env; ets = empty_ets_state
                     ; fo = empty_fo_graph };
    trace          = [];
    id             = 0;
    spec_chain_ids = [];
    history        = Semantics.Scheduler.empty_wake_history;
    wakers         = [];
    fresh_sleepers = [];
  } in
  (try
     let t0 = Unix.gettimeofday () in
     Semantics.Scheduler.explore mt sc;
     let elapsed_ms = int_of_float ((Unix.gettimeofday () -. t0) *. 1000.0) in
     Printf.printf "[time] %dms\n%!" elapsed_ms
   with Failure msg ->
     Printf.eprintf "Exploration error: %s\n" msg; exit 1)

(* ------------------------------------------------------------------ *)
(* Entry point                                                          *)
(* ------------------------------------------------------------------ *)

let () =
  if !eval_mode    then do_eval ()
  else if !explore_mode then do_explore ()
  else do_parse ()
