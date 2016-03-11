(******************************************************************************)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2015 --- OCamlPro                                   *)
(*     This file is distributed under the terms of the CeCILL-C licence       *)
(******************************************************************************)

(******************************************************************************)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*   This file is distributed under the terms of the CeCILL-C licence         *)
(******************************************************************************)

open Typed
open Lexing
open Format
open Options

module SAT = (val (Sat_solvers.get_current ()) : Sat_solvers.S)
module FE = Frontend.Make (SAT)

let timers = Timers.empty ()

let () =
  (* what to do with Ctrl+C ? *)
  Sys.set_signal Sys.sigint(*-6*)
    (Sys.Signal_handle (fun _ ->
      if Options.profiling() then Profiling.switch ()
      else (print_endline "User wants me to stop."; exit 1)
     )
    )

let () =
  if Options.profiling() then
    (* put the test here because Windows does not handle Sys.Signal_handle
       correctly *)
    List.iter
      (fun sign ->
        Sys.set_signal sign
          (Sys.Signal_handle
             (fun _ ->
               Profiling.print true (SAT.get_steps ()) timers fmt;
               exit 1
             )
          )
      )[ Sys.sigterm (*-11*); Sys.sigquit (*-9*)]

let () =
    Sys.set_signal Sys.sigprof (*-21*)
      (Sys.Signal_handle
         (fun _ ->
           if Options.profiling () then
             Profiling.print false (SAT.get_steps ()) timers fmt;
         )
      )

let processing report declss =
  SAT.reset_steps ();
  List.iter
       (fun cnf ->
	 ignore (Queue.fold (FE.process_decl report)
		   (SAT.empty (), true, Explanation.empty) cnf)
       ) declss

let _ =
  Options.Time.start ();
  Options.Time.set_timeout ();
  if Options.profiling () then begin
    Timers.reset timers;
    assert (Options.timers());
    Options.set_timer_start (Timers.start timers);
    Options.set_timer_pause (Timers.pause timers);
    Profiling.init ();
  end;

  (*Options.parse_args ();*)
  let file = get_file () in
  let cin = if file <> "" then open_in file else stdin in
  let lb = from_channel cin in
  try
    let d = FE.open_file lb cin in
    let d =
      List.map
        (fun d ->  Cnf.make (List.map (fun (f, env) -> f, true) d)) d in
    processing FE.print_status d;
    Options.Time.unset_timeout ();
    if Options.profiling() then
      Profiling.print true (SAT.get_steps ()) timers fmt;
  with
    | Why_lexer.Lexical_error s ->
      Loc.report err_formatter (lexeme_start_p lb, lexeme_end_p lb);
      eprintf "lexical error: %s\n@." s;
      exit 1
    | Parsing.Parse_error ->
      let  loc = (lexeme_start_p lb, lexeme_end_p lb) in
      Loc.report err_formatter loc;
      eprintf "syntax error\n@.";
      exit 1
    | Errors.Error(e,l) ->
      Loc.report err_formatter l;
      eprintf "typing error: %a\n@." Errors.report e;
      exit 1

