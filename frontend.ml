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
(*     Claire Dross                                                       *)
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


  let set_timeout () =
    if timelimit () <> 0. then
      ignore (Unix.setitimer Unix.ITIMER_REAL
		{ Unix.it_value = timelimit (); Unix.it_interval = 0. })
	
  let unset_timeout () =
    if timelimit () <> 0. then
      ignore (Unix.setitimer Unix.ITIMER_REAL
		{ Unix.it_value = 0.; Unix.it_interval = 0. })

end

type output = Unsat of Explanation.t | Inconsistent 
	      | Sat of Sat.t | Unknown of Sat.t

let check_produced_proof dep =
  if verbose () then 
    fprintf fmt "checking the proof:\n-------------------\n%a@." 
      Explanation.print_proof dep;

  try
    let env =
      (Formula.Set.fold
         (fun f env -> 
            Sat.assume env 
	      {Sat.f=f;age=0;name=None;mf=false;
	       gf=false; from_terms = []; inv=false}
         ) (Explanation.formulas_of dep) (Sat.empty ()))
    in
    raise (Sat.Sat env)
  with 
    | Sat.Unsat _  -> ()
    | (Sat.Sat _ | Sat.I_dont_know _) as e -> raise e

(* storing how many steps of selection hypothesis *)
let num_of_selection = ref 0

let process_decl ?(last_step = true) print_status (env, consistent, dep) d =
  try
    match d.st_decl with
      | Assume(f, mf, inv) -> 
	  Sat.assume env 
	    {Sat.f=f; age=0; name=None; 
	     mf=mf; gf=false; from_terms = []; inv=inv},
	  consistent, dep

      |	PredDef f -> 
	Sat.pred_def env f , consistent, dep

      | RwtDef r -> assert false

      | Query(n, f, lits, sort) ->
	  let dep = 
	    if consistent then
	      let dep' = Sat.unsat env 
		{Sat.f=f;age=0;name=None;
		 mf=(sort <> Check);gf=true; from_terms = []; inv=false} in
	      Explanation.union dep' dep
	    else dep
          in
          if debug_proof () then check_produced_proof dep;
	  print_status d (Unsat dep) (Sat.stop ());
	  env, consistent, dep
  with 
    | Sat.Sat t -> 
	if not last_step then raise (Sat.More_Hypotheses t);
	print_status d (Sat t) (Sat.stop ());
        if model () then Sat.print_model ~header:true std_formatter t;
	env , consistent, dep
    | Sat.Unsat dep' -> 
        let dep = Explanation.union dep dep' in
        if debug_proof () then check_produced_proof dep;
	print_status d Inconsistent (Sat.stop ());
	env , false, dep
    | Sat.I_dont_know t -> 
	if not last_step then raise (Sat.More_Hypotheses t);
	print_status d (Unknown t) (Sat.stop ());
        if model () then Sat.print_model ~header:true std_formatter t;
	env , consistent, dep

exception Parse_only

let rec add_theory env s =
  let c_in = open_in s in
  let lb = from_channel c_in in 
  try 
    let includes, a = Why_parser.file Why_lexer.token lb in
    let env = List.fold_left add_theory env includes in
    if parse_only () then raise Parse_only;
    let d, env = Why_typing.file true env a in
    close_in c_in;
    let d = List.map (fun (d, _) -> (d, true)) d in
    let cnf =  Cnf.make_theory d in
    let f = Queue.fold (fun formulas d ->
      match d.st_decl with
        | Assume (f, _, _ ) | PredDef f ->
          f :: formulas
        | RwtDef _ | Query _ -> assert false)
      [] cnf in
    Custom_theory.add_theory f;
    env
  with
    | Parse_only -> env
    | Why_lexer.Lexical_error s -> 
      Loc.report err_formatter (lexeme_start_p lb, lexeme_end_p lb);
      eprintf "lexical error in theory: %s\n@." s;
      exit 1
    | Parsing.Parse_error ->
      let  loc = (lexeme_start_p lb, lexeme_end_p lb) in
      Loc.report err_formatter loc;
      eprintf "syntax error in theory\n@.";
      exit 1
    | Common.Error(e,l) -> 
      Loc.report err_formatter l; 
      eprintf "typing error in theory: %a\n@." Common.report e;
      exit 1


let open_file file lb =
  let d ,status =
    if !smtfile then begin
      let bname,l,status = Smt_parser.benchmark Smt_lex.token lb in
      if verbose () then printf "converting smt file : ";
      let l = List.flatten (List.map Smt_to_why.bench_to_why l) in
      if verbose () then printf "done.@.";
      if parse_only () then exit 0;
      let ltd, _ = Why_typing.file false Why_typing.empty_env l in
      let lltd = Why_typing.split_goals ltd in
      lltd, status
    end
    else if !smt2file then begin
      let commands = Smtlib2_parse.main Smtlib2_lex.token lb in
      if verbose () then printf "converting smt2 file : ";
      let l = Smtlib2_to_why.smt2_to_why commands in
      if verbose () then printf "done.@.";
      if parse_only () then exit 0;
      let ltd, _ = Why_typing.file false Why_typing.empty_env l in
      let lltd = Why_typing.split_goals ltd in
      lltd, Smt_ast.Unknown
    end
    else
      let includes, a = Why_parser.file Why_lexer.token lb in
      (* Customized theories given as include *)
      let env = List.fold_left add_theory Why_typing.empty_env includes in
      if parse_only () then exit 0;
      let ltd, _ = Why_typing.file false env a in
      let lltd = Why_typing.split_goals ltd in
      lltd, Smt_ast.Unknown
  in
  if file <> " stdin" then close_in cin;
  if type_only () then exit 0;
  d, status

module StringSet = Selection.StringSet

let check_sub_str s1 s2 =
  try
    let len = String.length s2 in
    for i = 0 to String.length s1 - len do
      if String.sub s1 i len = s2 then raise Exit
    done;
    false
  with Exit -> true

let remove_last_selected_rules decls =
  List.filter
    (fun decl -> match decl.c with
      | TAxiom (_, name, _, _) ->
          List.for_all (fun substr -> not (check_sub_str name substr))
            (Options.last_selected ())
      | _ -> true
    ) decls

let print_debug_each_step new_rules depth selected_dcls =
  if debug () then
    begin
      let sort_list lst =
	let lst = StringSet.elements lst in
	List.sort (fun x y -> if x = y then 0 else if x > y then 1 else -1) lst
      in
      let sorted = sort_list new_rules in
      let size_new_rules = List.length sorted in
      fprintf fmt "\nDepth [%d] <select %d new rules>:@." depth size_new_rules;
      if verbose () then begin
        let suffix = "_dynamic_"^(string_of_int depth)^".why" in
        let filename = Selection.print_to_file selected_dcls ~same_order:true
            ~old_name:!Options.file ~suffix in
        fprintf fmt "Printing to file: %s@." filename;
        fprintf fmt "New rules: [%d] \n%s@."
            size_new_rules (String.concat " - " sorted);
      end;
      flush stdout
    end

let process_goal_internal ?(last_step = true) report decls =
  let cnf = Cnf.make decls in
  ignore (Queue.fold (process_decl ~last_step report)
            (Sat.empty_with_inst Sat.count_instantiated_axioms,
             true, Explanation.empty) cnf)

let process_goal ?(last_step = true) report decls =
  let decls = List.map (fun d -> d, true) decls in
  process_goal_internal ~last_step report decls

let process_last_selected report decls =
  try
    let decls = remove_last_selected_rules decls in
    if debug () then begin
      let suffix = 
        if simplify () then "_last-select-simplify.why" 
        else "_last-selected.why" in
      let filename = Selection.print_to_file decls ~same_order:true 
          ~old_name:!Options.file ~suffix in
      fprintf fmt "Printing to file: %s@." filename;
    end;
    process_goal ~last_step:false report decls
  with Sat.More_Hypotheses env ->
    process_goal report decls

let process_incremental_pruning report decls =
  let (graph, goal_name, goal_f) = Pruning.create_graph decls in
  let depth = ref 1 in
  let selected_names = ref (Pruning.pruning !depth goal_name goal_f graph) in
  let selected_dcls = ref (Pruning.selected_axioms decls !selected_names) in
  let new_names = ref (!selected_names) in
  let flag_continue = ref true in
  while !flag_continue do
    let current_selected = List.map fst !selected_dcls in
    print_debug_each_step !new_names !depth current_selected;
    num_of_selection := !depth;

    if List.length !selected_dcls = List.length decls then begin
      (* in the last step, don't use thresold max_instaces to prove*)
      (* just use the normal alt-ero *)
      Options.set_max_instances 0;
      process_goal report decls;
      flag_continue := false
    end
    else
      try
        process_goal_internal ~last_step:false report !selected_dcls;
        flag_continue := false;
      with Sat.More_Hypotheses env ->
        begin
          flag_continue := true;
          depth := !depth + 1;
          Sat.reset_tab_instantiated_axiom ~reset_high_axiom:false;
          let all_names = Pruning.pruning !depth goal_name goal_f graph in
          new_names := StringSet.diff all_names !selected_names;
          selected_names := all_names;
          let new_dcls = Pruning.selected_axioms decls all_names in
            if List.length !selected_dcls = List.length new_dcls then
              selected_dcls := List.map (fun d-> d,true) decls
            else
              selected_dcls := new_dcls
        end
  done

let process_selection report all_decls =
  if debug () then
    fprintf fmt "Starting the selection process with max_instantiate_num=%d@."
      (Options.max_instances ());

  (* we should call this function at the beginning *)
  (* otherwise we will get trouble in some case *)
  let _ = Cnf.make (List.map (fun d->d,true) all_decls) in
  
  let decls = remove_last_selected_rules all_decls in
  Selection.init_selection decls;

  let rec process_next depth axioms state =
    let new_axioms, new_state = Selection.next_selection axioms state in
    let total_axioms = StringSet.union axioms new_axioms in
    let selected_decls = 
      Selection.select_rules decls total_axioms ~include_logic_type:true in

    print_debug_each_step new_axioms depth selected_decls;
    num_of_selection := depth;

    if new_state = Selection.Last_Select then
      begin
	(* ??? why is there a special action here for max instances? *)
        (* in the last step, don't use thresold max_instaces to prove*)
        (* just use the normal alt-ero *)
        Options.set_max_instances 0;
        process_goal report all_decls
      end
    else
      try
        process_goal ~last_step:false report selected_decls
      with Sat.More_Hypotheses env ->
        begin
          Sat.reset_tab_instantiated_axiom ~reset_high_axiom:false;
          process_next (depth + 1) total_axioms new_state
        end
  in
  process_next 1 (Selection.extract_goals decls) Selection.Init

(* this version of process_selection with an initial 2s run of alt-ergo
   should ideally be supressed *)
(*
let process_selection report decls =
  let limit_step = (-1) in
  let limit_sec = (2.0) in
  Options.set_step_limit limit_step;
  Selection.set_internal_timeout limit_sec;
  Selection.start_timer ();
  if debug () then begin
    fprintf fmt "Try to prove with normal alt-ergo with step=%d or time=%f sec@."
      limit_step limit_sec;
    let filename = Selection.print_to_file false decls
        !Options.file ("_simplify.why") in
    fprintf fmt "Printing to file: %s@." filename;
  end;
  try
    process_goal ~last_step:false report decls
  with Sat.More_Hypotheses env ->
    (* call the version of process_selection without the initial run *)
    Options.set_step_limit (-1);
    Selection.set_internal_timeout (-1.0);
    Sat.reset_tab_instantiated_axiom ~reset_high_axiom:false;
    process_selection report decls
*)

let process_selection_in_sat report decls =
  let decls = remove_last_selected_rules decls in
  let starting_depth = 3 in
  Selection_sat.init_selection decls;
  Selection_sat.set_depth 1;
  ignore (Selection_sat.get_init_rules ());
  let count = ref 2 in
  while !count <= starting_depth do
    ignore(Selection_sat.get_new_rules ());
    count := !count + 1
  done;
  let init_decls = Selection_sat.get_rules_in_table
        ~start_depth:1 ~end_depth:starting_depth in
  let cnf = Cnf.make (List.map (fun d -> d, true) init_decls) in
  ignore (Queue.fold (process_decl report)
        (Sat.empty (), true, Explanation.empty) cnf)

let pruning = 
  List.map
    (fun d -> 
       if select () > 0 then Pruning.split_and_prune (select ()) d 
       else [List.map (fun f -> f,true) d])
    
let processing report declss = 
  Sat.start ();
  let declss = List.map (List.map fst) declss in
  (* The preprocessing will hopefully be moved to Why3 *)
  let declss =
    List.map
      (fun d -> if simplify () then Simplify.preprocessing d else d) declss
  in
  (* initial selection of hypotheses and axioms *)
  if select () > 0 then
    List.iter (List.iter (process_goal_internal report))
      (List.map (Pruning.split_and_prune (select ())) declss)

  (* repeat initial selection of hypotheses and axioms, starting at depth 1
     and incrementing the depth *)
  else if select () = -1 then
    List.iter (process_incremental_pruning report) declss

  (* auto-selection of hypotheses and axioms *)
  else if autoselect () then
    List.iter (process_selection report) declss

  (* auto-selection in SAT of hypotheses and axioms *)
  else if autoselect_sat () then
    List.iter (process_selection_in_sat report) declss

  (* do a first run without the axioms to select last, then a regular run *)
  else if Options.last_selected () <> [] then
    List.iter (process_last_selected report) declss

  (* do a regular run *)
  else
    List.iter (process_goal report) declss

let print_status d s steps =
  let result_select =
    if (!num_of_selection > 0) then "("^string_of_int(!num_of_selection)^")"
    else "" in
  let satmode = !smtfile or !smt2file or !satmode in 
  match s with
    | Unsat dep -> 
	if not satmode then Loc.report std_formatter d.st_loc;
	if satmode then printf "@{<C.F_Red>unsat@}@." 
	else printf "@{<C.F_Green>Valid@} (%2.4f) (%Ld) %s@." (Time.get()) steps result_select;
	if proof () && not (debug_proof ()) then 
          printf "Proof:\n%a@." Explanation.print_proof dep
	  
    | Inconsistent ->
	if not satmode then 
	  (Loc.report std_formatter d.st_loc; 
	   fprintf fmt "Inconsistent assumption@.")
	else printf "unsat@."
	  
    | Unknown t ->
	if not satmode then
	  (Loc.report std_formatter d.st_loc; printf "I don't know.@.")
	else printf "unknown@."
	  
    | Sat t -> 
	if not satmode then Loc.report std_formatter d.st_loc;
	if satmode then printf "unknown (sat)@." 
	else printf "I don't know@."


let main _ =
  Time.set_timeout ();
  let lb = from_channel cin in 
  try 
    let d, status = open_file !file lb in 
    processing print_status d;
    Time.unset_timeout ();
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
