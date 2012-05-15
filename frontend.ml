(**************************************************************************)
(*                                                                        *)
(*     The Alt-Ergo theorem prover                                        *)
(*     Copyright (C) 2006-2011                                            *)
(*                                                                        *)
(*     Sylvain Conchon                                                    *)
(*     Evelyne Contejean                                                  *)
(*                                                                        *)
(*     Francois Bobot                                                     *)
(*     Mohamed Iguernelala                                                *)
(*     Stephane Lescuyer                                                  *)
(*     Alain Mebsout                                                      *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

open Why_ptree

let _ = 
  Sys.set_signal Sys.sigint 
    (Sys.Signal_handle 
       (fun _ -> print_endline "User wants me to stop."; exit 1))

open Lexing
open Format
open Options

module Time = struct

  open Unix
    
  let u = ref 0.0
    
  let start () = u:=(times()).tms_utime

  let get () = 
    let res = (times()).tms_utime -. !u in
    start();
    res

end

type output = Unsat of Explanation.t | Inconsistent | Sat | Unknown

let check_produced_proof dep =
  if verbose () then 
    fprintf fmt "checking the proof:\n-------------------\n%a@." 
      Explanation.print_proof dep;

  try
    let env =
      (Formula.Set.fold
         (fun f env -> 
            Sat.assume env {Sat.f=f;age=0;name=None;mf=false;gf=false}
         ) (Explanation.formulas_of dep) Sat.empty)
    in
    raise (Sat.Sat env)
  with 
    | Sat.Unsat _  -> ()
    | (Sat.Sat _ | Sat.I_dont_know _) as e -> raise e


let process_decl print_status (env, consistent, dep) d =
  try
    match d.st_decl with
      | Assume(f,mf) -> 
	  Sat.assume env {Sat.f=f;age=0;name=None;mf=mf;gf=false},
	  consistent, dep

      |	PredDef f -> 
	Sat.pred_def env f , consistent, dep

      | RwtDef r -> assert false

      | Query(n, f, lits)-> 
	  let dep = 
	    if consistent then
	      let dep' = Sat.unsat env 
		{Sat.f=f;age=0;name=None;mf=true;gf=true} in
	      Explanation.union dep' dep
	    else dep
          in
          if debug_proof () then check_produced_proof dep;
	  print_status d (Unsat dep) (Sat.stop ());
	  env, consistent, dep
  with 
    | Sat.Sat t -> 
	print_status d Sat (Sat.stop ());
        if model () then Sat.print_model std_formatter t;
	env , consistent, dep
    | Sat.Unsat dep' -> 
        let dep = Explanation.union dep dep' in
        if debug_proof () then check_produced_proof dep;
	print_status d Inconsistent (Sat.stop ());
	env , false, dep
    | Sat.I_dont_know t -> 
	print_status d Unknown (Sat.stop ());
        if model () then Sat.print_model std_formatter t;
	env , consistent, dep

let open_file file lb =
  let d ,status =
    if !smtfile then begin
      let bname,l,status = Smt_parser.benchmark Smt_lex.token lb in
      if verbose () then printf "converting smt file : ";
      let l = List.flatten (List.map Smt_to_why.bench_to_why l) in
      if verbose () then printf "done.@.";
      if parse_only () then exit 0;
      let ltd = Why_typing.file (l) in
      let lltd = Why_typing.split_goals ltd in
      lltd, status
    end
    else if !smt2file then begin
      let commands = Smtlib2_parse.main Smtlib2_lex.token lb in
      if verbose () then printf "converting smt2 file : ";
      let l = Smtlib2_to_why.smt2_to_why commands in
      if verbose () then printf "done.@.";
      if parse_only () then exit 0;
      let ltd = Why_typing.file l in
      let lltd = Why_typing.split_goals ltd in
      lltd, Smt_ast.Unknown
    end
    else
      let a = Why_parser.file Why_lexer.token lb in
      if parse_only () then exit 0;
      let ltd = Why_typing.file a in
      let lltd = Why_typing.split_goals ltd in
      lltd, Smt_ast.Unknown
  in
  if file <> " stdin" then close_in cin;
  if type_only () then exit 0;
  d, status

let pruning = 
  List.map
    (fun d -> 
       if select () > 0 then Pruning.split_and_prune (select ()) d 
       else [List.map (fun f -> f,true) d])
    
let processing report declss = 
  Sat.start ();
  let declss = List.map (List.map fst) declss in
  List.iter
    (List.iter 
       (fun dcl ->
	  let cnf = Cnf.make dcl in 
	  ignore (Queue.fold (process_decl report)
		    (Sat.empty, true, Explanation.empty) cnf)
       )) (pruning declss)


let print_status d s steps =
  let satmode = !smtfile or !smt2file or !satmode in 
  match s with
    | Unsat dep -> 
	if not satmode then Loc.report std_formatter d.st_loc;
	if satmode then printf "@{<C.F_Red>unsat@}@." 
	else printf "@{<C.F_Green>Valid@} (%2.4f) (%Ld)@." (Time.get()) steps;
	if proof () && not (debug_proof ()) then 
          printf "Proof:\n%a@." Explanation.print_proof dep
	  
    | Inconsistent ->
	if not satmode then 
	  (Loc.report std_formatter d.st_loc; 
	   fprintf fmt "Inconsistent assumption@.")
	else printf "unsat@."
	  
    | Unknown ->
	if not satmode then
	  (Loc.report std_formatter d.st_loc; printf "I don't know.@.")
	else printf "unknown@."
	  
    | Sat  -> 
	if not satmode then Loc.report std_formatter d.st_loc;
	if satmode then printf "unknown (sat)@." 
	else printf "I don't know@."


let main _ = 
  let lb = from_channel cin in 
  try 
    let d, status = open_file !file lb in 
    processing print_status d
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
    | Common.Error(e,l) -> 
	Loc.report err_formatter l; 
	eprintf "typing error: %a\n@." Common.report e;
	exit 1
