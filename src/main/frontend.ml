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
    (Commands.sat_tdecl -> output -> int64 -> 'a) ->
    sat_env * bool * Explanation.t -> Commands.sat_tdecl ->
    sat_env * bool * Explanation.t

  val open_file:
    Lexing.lexbuf -> in_channel ->
    ((int tdecl, int) annoted * Why_typing.env) list list

  val print_status : Commands.sat_tdecl -> output -> int64 -> unit
end

module Make(SAT : Sat_solvers.S) : S with type sat_env = SAT.t = struct

  type sat_env = SAT.t

  type output = Unsat of Explanation.t | Inconsistent
	        | Sat of sat_env | Unknown of sat_env

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
                 age=0;
                 lem=None;
	         mf=(sort <> Check);
                 gf=true;
                 from_terms = []
                } in
	      Explanation.union dep' dep
	    else dep
          in
          if debug_proof () then check_produced_proof dep;
          if save_used_context () then do_save_used_context env dep;
	  print_status d (Unsat dep) (SAT.get_steps ());
	  env, consistent, dep
    with
      | SAT.Sat t ->
        print_status d (Sat t) (SAT.get_steps ());
        if model () then SAT.print_model ~header:true std_formatter t;
        env , consistent, dep
      | SAT.Unsat dep' ->
        let dep = Explanation.union dep dep' in
        if debug_proof () then check_produced_proof dep;
        print_status d Inconsistent (SAT.get_steps ());
        env , false, dep
      | SAT.I_dont_know t ->
        print_status d (Unknown t) (SAT.get_steps ());
        if model () then SAT.print_model ~header:true std_formatter t;
        env , consistent, dep

  exception Parse_only

  let open_file lb cin =
    let file = Options.get_file() in
    let a = Why_parser.file Why_lexer.token lb in
    if parse_only () then exit 0;
    Parsing.clear_parser ();
    let ltd, typ_env = Why_typing.file false Why_typing.empty_env a in
    let d = Why_typing.split_goals ltd in
    if file <> " stdin" then close_in cin;
    if type_only () then exit 0;
    d

  let print_status d status steps =
    let time = Time.value() in
    let loc = d.st_loc in
    match status with
    | Unsat dep ->
      if js_mode () then
        printf "# [answer] Valid (%2.4f seconds) (%Ld steps)@." time steps
      else begin
        begin
          if Options.backward_compat() then
            printf "%aValid (%2.4f) (%Ld)@." Loc.report loc time steps
          else
            printf "%aValid (%2.4f) (%Ld steps)@." Loc.report loc time steps
        end;
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
        if Options.backward_compat() then
          printf "%aI don't know.@." Loc.report loc
        else
          printf "%aI don't know (%2.4f) (%Ld steps)@." Loc.report loc time steps

end
