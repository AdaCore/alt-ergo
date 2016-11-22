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
open Commands
open Lexing
open Format
open Options


module type S = sig

  type sat_env

  type output = Unsat of Explanation.t | Inconsistent
	        | Sat of sat_env | Unknown of sat_env

  val process_decl:
    (Commands.sat_tdecl -> output -> int64 -> unit) ->
    sat_env * bool * Explanation.t -> Commands.sat_tdecl ->
    sat_env * bool * Explanation.t

  val parse_and_typecheck:
    string -> Lexing.lexbuf option ->
    ((int tdecl, int) annoted * Why_typing.env) list list

  val print_status : Commands.sat_tdecl -> output -> int64 -> unit
end

module Make(SAT : Sat_solvers.S) : S with type sat_env = SAT.t = struct

  type sat_env = SAT.t

  type output = Unsat of Explanation.t | Inconsistent
	        | Sat of sat_env | Unknown of sat_env

  let get_steps () =
    if Int64.compare (SAT.get_steps ()) (Steps.stop ()) > 0
    then SAT.get_steps () else Steps.stop ()

  let check_produced_proof dep =
    if verbose () then
      fprintf fmt "checking the proof:\n-------------------\n%a@."
        Explanation.print_proof dep;

    try
      let pb = Formula.Set.elements (Explanation.formulas_of dep) in
      let env =
        List.fold_left
          (fun env f ->
            SAT.assume env
	      {Formula.f=f;
               trigger_depth = max_int;
               nb_reductions = 0;
               age=0;
               lem=None;
               mf=false;
	       gf=false;
               from_terms = []
              }
          ) (SAT.empty ()) pb
      in
      ignore (SAT.unsat
                env
    	        {Formula.f=Formula.vrai;
                 trigger_depth = max_int;
                 nb_reductions = 0;
                 age=0;
                 lem=None;
                 mf=false;
	         gf=false;
                 from_terms = []
                });
      fprintf fmt "Checking produced proof failed!@.";
      fprintf fmt "this may be due to a bug.@.";
      exit 1
    with
      | SAT.Unsat _  -> ()
      | (SAT.Sat _ | SAT.I_dont_know _) as e -> raise e


  let do_save_used_context env dep =
    if not (Options.js_mode ()) then
      let used, unused = SAT.retrieve_used_context env dep in
      let f = Options.get_used_context_file () in
      let cout = open_out f in
      List.iter (fun f ->
        match Formula.view f with
        | Formula.Lemma {Formula.name=name} ->
          output_string cout (sprintf "%s\n" name)
        | _ -> assert false
      ) used;
      close_out cout

  let process_decl print_status (env, consistent, dep) d =
    try
      match d.st_decl with
        | Assume(f, mf) ->
          if consistent then
	    SAT.assume env
	      {Formula.f=f;
               trigger_depth = max_int;
               nb_reductions = 0;
               age=0;
               lem=None;
	       mf=mf;
               gf=false;
               from_terms = []
              },
	    consistent, dep
          else env, consistent, dep
        | PredDef (f, name) ->
	  SAT.pred_def env f name d.st_loc, consistent, dep

        | RwtDef r -> assert false

        | Query(n, f, lits, sort) ->
	  let dep =
	    if consistent then
	      let dep' = SAT.unsat env
	        {Formula.f=f;
                 trigger_depth = max_int;
                 nb_reductions = 0;
                 age=0;
                 lem=None;
	         mf=(sort != Check);
                 gf=true;
                 from_terms = []
                } in
	      Explanation.union dep' dep
	    else dep
          in
          if debug_proof () then check_produced_proof dep;
          if save_used_context () then do_save_used_context env dep;
	  print_status d (Unsat dep) (get_steps ());
	  env, consistent, dep
    with
      | SAT.Sat t ->
        print_status d (Sat t) (get_steps ());
        if model () then SAT.print_model ~header:true std_formatter t;
        env , consistent, dep
      | SAT.Unsat dep' ->
        let dep = Explanation.union dep dep' in
        if debug_proof () then check_produced_proof dep;
        print_status d Inconsistent (get_steps ());
        env , false, dep
      | SAT.I_dont_know t ->
        print_status d (Unknown t) (get_steps ());
        if model () then SAT.print_model ~header:true std_formatter t;
        env , consistent, dep

  exception Parse_only

  (* pre-condition: f is of the form f'.zip *)
  let extract_zip_file f =
    let cin = MyZip.open_in f in
    try
      match MyZip.entries cin with
      | [e] when not (MyZip.is_directory e) ->
         if verbose () then
           eprintf
             "I'll read the content of '%s' in the given zip@."
             (MyZip.filename e);
         let content = MyZip.read_entry cin e in
         MyZip.close_in cin;
         content
      | _ ->
         MyZip.close_in cin;
         raise (Arg.Bad
                  (sprintf "%s '%s' %s@?"
                           "The zipped file" f
                           "should contain exactly one file."))
    with e ->
      MyZip.close_in cin;
      raise e

  let close_and_exit opened_cin cin retcode =
    if opened_cin then close_in cin;
    exit retcode

  (* lb_opt is set in to Some lb in JavaScript mode *)
  let parse_and_typecheck file lb_opt =
    let cin, lb, opened_cin =
      match lb_opt, Filename.check_suffix file ".zip" with
      | None, false ->
         if Pervasives.(<>) file "" then
           let cin = open_in file in
           cin, from_channel cin, true
         else stdin, from_channel stdin, false

      | None, true ->
         let file_content = extract_zip_file file in
         stdin, from_string file_content, false

      | Some lb, false ->
         stdin, lb, false

      | Some lb, true ->
         eprintf "Error: Zip files are not supported in JS mode !@.";
         exit 1
    in
    try
      let a = Why_parser.file Why_lexer.token lb in
      Parsing.clear_parser ();
      if parse_only () then close_and_exit opened_cin cin 0;
      let ltd, typ_env = Why_typing.file false Why_typing.empty_env a in
      let d = Why_typing.split_goals ltd in
      if type_only () then close_and_exit opened_cin cin 0;
      if opened_cin then close_in cin;
      d
    with
       | Why_lexer.Lexical_error s ->
          Loc.report err_formatter (lexeme_start_p lb, lexeme_end_p lb);
          eprintf "lexical error: %s\n@." s;
          close_and_exit opened_cin cin 1

       | Parsing.Parse_error ->
          let  loc = (lexeme_start_p lb, lexeme_end_p lb) in
          Loc.report err_formatter loc;
          eprintf "syntax error\n@.";
          close_and_exit opened_cin cin 1

       | Errors.Error(e,l) ->
          Loc.report err_formatter l;
          eprintf "typing error: %a\n@." Errors.report e;
          close_and_exit opened_cin cin 1


  let print_status d status steps =
    let time = Time.value() in
    let loc = d.st_loc in
    match status with
    | Unsat dep ->
      if js_mode () then
        printf "# [answer] Valid (%2.4f seconds) (%Ld steps)@." time steps
      else begin
        printf "%aValid (%2.4f) (%Ld steps)@." Loc.report loc time steps;
        if proof () && not (debug_proof ()) && not (save_used_context ()) then
          printf "Proof:\n%a@." Explanation.print_proof dep
      end

    | Inconsistent ->
      if js_mode () then
        printf "# [message] Inconsistent assumption \n@."
      else
        eprintf "%aInconsistent assumption@." Loc.report loc;

    | Unknown t | Sat t ->
      if js_mode () then
        printf "# [answer] unknown (%2.4f seconds) (%Ld steps)@." time steps
      else
        printf "%aI don't know (%2.4f) (%Ld steps)@." Loc.report loc time steps

end
