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

open Options
open Format

module type S = sig
  type t

  exception Sat of t
  exception Unsat of Explanation.t
  exception I_dont_know of t

  (* the empty sat-solver context *)
  val empty : unit -> t
  val empty_with_inst : (Formula.t -> bool) -> t

  (* [assume env f] assume a new formula [f] in [env]. Raises Unsat if
     [f] is unsatisfiable in [env] *)
  val assume : t -> Formula.gformula -> t

  (* [pred_def env f] assume a new predicate definition [f] in [env]. *)
  val pred_def : t -> Formula.t -> string -> Loc.t -> t

  (* [unsat env f size] checks the unsatisfiability of [f] in
     [env]. Raises I_dont_know when the proof tree's height reaches
     [size]. Raises Sat if [f] is satisfiable in [env] *)
  val unsat : t -> Formula.gformula -> Explanation.t

  val print_model : header:bool -> Format.formatter -> t -> unit

  val reset_steps : unit -> unit
  val get_steps : unit -> int64

  (* returns used axioms/predicates * unused axioms/predicates *)
  val retrieve_used_context :
    t -> Explanation.t -> Formula.t list * Formula.t list
end

(*** Implementation of Dfs_sat ***)
module Dfs_sat : S = struct

  module Th = Theory.Main
  open Sig
  module A = Literal
  module F = Formula
  module Inst = Matching.Make(Th)
  module SF = F.Set
  module MF = F.Map
  module Ex = Explanation

  let steps = ref 0L
  module H = Hashtbl.Make(Formula)


  module Heuristics = struct

    type t =
        {
          mp : float MF.t;

          (* valeur de l'increment pour l'activite des variables *)
          var_inc : float;

          (* inverse du facteur d'acitivte des vars, vaut 1/0.999 par defaut *)
          var_decay : float;
        }

    let empty () =
      {
        mp = MF.empty;
        var_inc = 1.;
        var_decay = 1. /. 0.95;
      }

    let bump_activity ({mp=mp;var_inc=var_inc} as env) expl =
      let stable = ref true in
      let mp =
        SF.fold
          (fun f mp ->
            let w = var_inc +. try MF.find f mp with Not_found -> 0. in
            stable := !stable && w <= 1e100;
            MF.add f w mp
          )(Ex.bj_formulas_of expl) mp
      in
      let mp =
        if !stable then  mp
        else MF.fold (fun f w acc -> MF.add f (w *. 1e-100) acc) mp MF.empty
      in
      { env with mp = mp; var_inc = var_inc *. env.var_decay }

    let choose l0 env =
      let l =
        List.rev_map
          (fun ((a,b,d) as e) ->
            e, (try (MF.find a.F.f env.mp) with Not_found -> 0.), a.F.gf
          ) l0
      in
      let l =
        List.fast_sort
          (fun (_, x1, b1) (_, x2, b2) ->
            let c = Pervasives.compare b2 b1 in
            if c <> 0 then c
            else Pervasives.compare x2 x1
          )l
      in
      let e, cpt, _ = List.hd l in
      e, List.rev (List.rev_map (fun (e,_,_) -> e) (List.tl l))

  end


  type t = {
    (* The field gamma contains the current Boolean model (true formulas) of
       the SAT. Each assumed formula is mapped to a tuple (gf, ex, dlvl, plvl),
       where:
       - gf is the rich form of the formula
       - ex is the explanation associated to the formula
       - dlvl is the decision level where the formula was assumed to true
       - plvl is the propagation level (w.r.t. dlvl) of the formula.
       It forms with dlvl a total ordering on the formulas in gamma.
    *)
    gamma : (F.gformula * Ex.t * int * int) MF.t;

    delta : (F.gformula * F.gformula * Ex.t) list;
    dlevel : int;
    plevel : int;
    ilevel : int;
    tbox : Th.t;
    unit_tbox : Th.t; (* theory env of facts at level 0 *)
    inst : Inst.t;
    heuristics : Heuristics.t ref;
    ground_preds : (F.gformula * string * Loc.t) Term.Map.t;
    add_inst: Formula.t -> bool;
  }

  exception Sat of t
  exception Unsat of Ex.t
  exception I_dont_know of t
  exception IUnsat of Ex.t * Term.Set.t list


  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct

    let propagations (env, bcp, tcp, ap_delta, lits) =
      if debug_sat() then begin
        fprintf fmt
          "[sat] propagations: |lits| = %d , B = %b , T = %b , "
          (List.length lits) bcp tcp ;
        fprintf fmt "|Delta| = %d, |ap_Delta| = %d@."
          (List.length env.delta) (List.length ap_delta)
      end

    let is_it_unsat gf =
      if verbose () && debug_sat () then
        let s =
          match F.view gf.F.f with
            | F.Lemma _   -> "lemma"
            | F.Clause _  -> "clause"
            | F.Unit _    -> "conjunction"
            | F.Skolem _  -> "skolem"
            | F.Literal _ -> "literal"
            | F.Let _     -> "let"
        in
        fprintf fmt "[sat] the following %s is unsat ? :@.%a@.@."
          s F.print gf.F.f

    let pred_def f =
      if debug_sat () then
        eprintf "[sat] I assume a predicate: %a@.@." F.print f

    let unsat_rec dep =
      if debug_sat () then fprintf fmt "unsat_rec : %a@." Ex.print dep

    let assume gf dep env =
      if debug_sat () then
        let {F.f=f;age=age;lem=lem;mf=mf;from_terms=terms} = gf in
        fprintf fmt "[sat] at level (%d, %d) I assume a " env.dlevel env.plevel;
        begin match F.view f with
        | F.Literal a ->
	  Term.print_list str_formatter terms;
	  let s = flush_str_formatter () in
	  let n = match lem with
	    | None -> ""
	    | Some ff ->
	      (match F.view ff with F.Lemma xx -> xx.F.name | _ -> "")
	  in
	  fprintf fmt "LITERAL (%s : %s) %a@." n s Literal.LT.print a;
          fprintf fmt "==========================================@.@."

        | F.Unit _   -> fprintf fmt "conjunction@."
        | F.Clause _ -> fprintf fmt "clause %a@." F.print f
        | F.Lemma _  -> fprintf fmt "%d-atom lemma \"%a\"@." (F.size f) F.print f
        | F.Skolem _ -> fprintf fmt "skolem %a@." F.print f
        | F.Let {F.let_var=lvar; let_term=lterm; let_f=lf} ->
	  fprintf fmt "let %a = %a in %a@."
	    Symbols.print lvar Term.print lterm F.print lf
        end;
	if verbose () then
          fprintf fmt "with explanations : %a@." Explanation.print dep

    let unsat () =
      if debug_sat () then fprintf fmt "[sat] unsat@."

    let decide f env =
      if debug_sat () then
        fprintf fmt "[sat] I decide: at level (%d, %d), on %a@."
          env.dlevel env.plevel F.print f

    let instantiate env =
      if debug_sat () then
        fprintf fmt "[sat] I instantiate at level (%d, %d). Inst level = %d@."
          env.dlevel env.plevel env.ilevel

    let backtracking f env =
      if debug_sat () then
        fprintf fmt "[sat] backtrack: at level (%d, %d), and assume not %a@."
          env.dlevel env.plevel F.print f

    let backjumping f env =
      if debug_sat () then
        fprintf fmt
          "[sat] backjump: at level (%d, %d), I ignore the case %a@."
          env.dlevel env.plevel F.print f

    let elim _ _ =
      if debug_sat () && verbose () then fprintf fmt "[sat] elim@."

    let red _ _ =
      if debug_sat () && verbose () then fprintf fmt "[sat] red@."

    let delta d =
      if debug_sat () && verbose () && false then begin
        fprintf fmt "[sat] - Delta ---------------------@.";
        List.iter (fun (f1, f2, ex) ->
	  fprintf fmt "(%a or %a), %a@."
            F.print f1.F.f F.print f2.F.f Ex.print ex) d;
        fprintf fmt "[sat] --------------------- Delta -@."
      end

    let gamma g =
      if debug_sat () && verbose () then begin
        fprintf fmt "[sat] --- GAMMA ---------------------@.";
        MF.iter (fun f (_, ex, dlvl, plvl) ->
	  fprintf fmt  "(%d, %d) %a \t->\t%a@."
            dlvl plvl F.print f Ex.print ex) g;
        fprintf fmt "[sat] - / GAMMA ---------------------@.";
      end

    let bottom classes =
      if bottom_classes () then
        printf "bottom:%a\n@." Term.print_tagged_classes classes

    let inconsistent expl env =
      if debug_sat () then
        fprintf fmt "inconsistent at level (%d, %d), reason : %a@."
          env.dlevel env.plevel Ex.print expl

  end
  (*BISECT-IGNORE-END*)

  let selector env f orig =
    not (MF.mem f env.gamma)
    && begin match F.view orig with
      | F.Lemma _ -> env.add_inst orig
      | _ -> true
    end

  let is_literal f = match F.view f with F.Literal _ -> true | _ -> false

  let extract_prop_model t =
    let s = ref SF.empty in
    MF.iter
      (fun f _ ->
        if (complete_model () && is_literal f) || F.is_in_model f then
	  s := SF.add f !s
      )
      t.gamma;
    !s

  let print_prop_model fmt s =
    SF.iter (fprintf fmt "\n %a" F.print) s

  let print_model ~header fmt t =
    Format.print_flush ();
    if header then fprintf fmt "\nModel\n@.";
    let pm = extract_prop_model t in
    if not (SF.is_empty pm) then begin
      fprintf fmt "Propositional:";
      print_prop_model fmt pm;
      fprintf fmt "\n@.";
    end;
    Th.print_model fmt t.tbox


  let _ =
    if not (model ()) then
      try
        Sys.set_signal Sys.sigalrm
	  (Sys.Signal_handle (fun _ -> Options.exec_timeout ()))
      with Invalid_argument _ -> ()

  let refresh_model_handler =
    if model () then
      fun t ->
        try
	  Sys.set_signal Sys.sigalrm
	    (Sys.Signal_handle (fun _ ->
	      printf "%a@." (print_model ~header:true) t;
	      Options.exec_timeout ()))
        with Invalid_argument _ -> ()
    else fun _ -> ()

  (* sat-solver *)

  let b_elim f env =
    try
      let _ = MF.find f env.gamma in
      Options.tool_req 2 "TR-Sat-Bcp-Elim-1";
      if Options.profiling() then Profiling.elim true;
      true
    with Not_found -> false

  let th_elim f env =
    match F.view f with
      | F.Literal a ->
        assert (A.LT.is_ground a);
        if Th.query a env.tbox = No then false
        else begin
          Options.tool_req 2 "TR-Sat-Bcp-Elim-2";
          if Options.profiling() then Profiling.elim false;
          true
        end
      | _ -> false

  let red f env tcp =
    let nf = F.mk_not f in
    try
      let _, ex, _, _ = MF.find nf env.gamma in
      let r = Yes (ex, Th.cl_extract env.tbox) in
      Options.tool_req 2 "TR-Sat-Bcp-Red-1";
      r, true
    with Not_found ->
      if not tcp then No, false
      else match F.view nf with
      | F.Literal a ->
        assert (A.LT.is_ground a);
        let ans = Th.query a env.tbox in
        if ans <> No then Options.tool_req 2 "TR-Sat-Bcp-Red-2";
        ans, false
      | _ -> No, false

  let pred_def env f name loc =
    let ff =
      { F.f = f;
        age = 0;
        lem = None;
        mf = true;
        gf = false;
        from_terms = []
      }
    in
    Debug.pred_def f;
    let t = Term.make (Symbols.name name) [] Ty.Tbool in
    if Term.Set.mem t (F.ground_terms_rec f) then begin
      assert (not (Term.Map.mem t env.ground_preds));
      {env with ground_preds = Term.Map.add t (ff, name, loc) env.ground_preds}
    end
    else
    {env with inst = Inst.add_predicate env.inst ff}


  let add_dep f dep =
    match F.view f with
      | F.Literal _ when proof () ->
        if not (Ex.mem (Ex.Bj f) dep) then
	  Ex.union (Ex.singleton (Ex.Dep f)) dep
        else dep
      | F.Clause _ when proof () ->
        Ex.union (Ex.singleton (Ex.Dep f)) dep
      | _ -> dep


  let rec add_dep_of_formula f dep =
    let dep = add_dep f dep in
    match F.view f with
      | F.Unit (f1, f2) when proof () ->
        add_dep_of_formula f2 (add_dep_of_formula f1 dep)
      | _ -> dep

  let do_bcp env tcp delta acc =
    let tcp = tcp && not (Options.no_tcp ()) in
    List.fold_left
      (fun (cl,u) ((({F.f=f1} as gf1), ({F.f=f2} as gf2), d) as fd) ->
        Debug.elim gf1 gf2;
	if b_elim f1 env ||  b_elim f2 env ||
          (tcp && (th_elim f1 env || th_elim f2 env)) then (cl,u)
	else
          begin
            Debug.red gf1 gf2;
	    match red f1 env tcp, red f2 env tcp with
	    | (Yes (d1, c1), b1) , (Yes (d2, c2), b2) ->
              if Options.profiling() then Profiling.bcp_conflict b1 b2;
	      let expl = Ex.union (Ex.union d d1) d2 in
              let c = List.rev_append c1 c2 in
	      raise (Exception.Inconsistent (expl, c))

            | (Yes(d1, _), b) , (No, _) ->
              if Options.profiling() then Profiling.red b;
              cl, (gf2,Ex.union d d1) :: u

	    | (No, _) , (Yes(d2, _),b) ->
              if Options.profiling() then Profiling.red b;
              cl, (gf1,Ex.union d d2) :: u

	    | (No, _) , (No, _) -> fd::cl , u
          end
      ) acc delta


  let dummy_gf mf gf =
    { F.f= F.vrai;
      age= 0;
      lem= None;
      from_terms = [];
      mf= mf;
      gf= gf }

  let theory_assume env facts =
    Options.tool_req 2 "TR-Sat-Assume-Lit";
    if facts = [] then env
    else
      let facts, ufacts, inst, mf, gf =
        List.fold_left
          (fun (facts, ufacts, inst, mf, gf) (a, ff, ex, dlvl, plvl) ->
            assert (A.LT.is_ground a);
            let facts = (a, ex, dlvl, plvl) :: facts in
            let ufacts =
              if Ex.has_no_bj ex then (a, ex, dlvl, plvl) :: ufacts
              else ufacts
            in
            if not ff.F.mf then begin
              fprintf fmt "%a@." F.print ff.F.f;
              assert false
            end;
            let inst =
              if ff.F.mf then Inst.add_terms inst (A.LT.terms_nonrec a) ff
              else inst
            in
            facts, ufacts, inst, mf || ff.F.mf, gf || ff.F.gf
          )([], [], env.inst, false, false) facts
      in
      let utbox, _, _ = (* assume unit facts in the theory *)
        if ufacts <> [] then
          try Th.assume ~ordered:false ufacts env.unit_tbox
          with Exception.Inconsistent (reason, _) as e ->
            assert (Ex.has_no_bj reason);
            if Options.profiling() then Profiling.theory_conflict();
            if debug_sat() then fprintf fmt "[sat] solved by unit_tbox@.";
            raise e
        else env.unit_tbox, Term.Set.empty, 0
      in
      let tbox, new_terms, cpt =
        try Th.assume facts env.tbox
        with Exception.Inconsistent _ as e ->
          if Options.profiling() then Profiling.theory_conflict();
          raise e
      in
      let inst = Inst.add_terms inst new_terms (dummy_gf mf gf) in
      steps := Int64.add (Int64.of_int cpt) !steps;
      if steps_bound () <> -1
        && Int64.compare !steps (Int64.of_int (steps_bound ())) > 0 then
        begin
	  printf "Steps limit reached: %Ld@." !steps;
	  exit 1
        end;
      { env with tbox = tbox; unit_tbox = utbox; inst = inst }

  let propagations ((env, bcp, tcp, ap_delta, lits) as result) =
    let env = theory_assume env lits in
    Debug.propagations result;
    let acc =
      if bcp then do_bcp env tcp env.delta ([], [])
      else env.delta, [] (* no even bcp for old clauses *)
    in
    (*both bcp and tcp set to true for new clauses*)
    let delta, unit = do_bcp env true ap_delta acc in
    {env with delta = delta}, unit

  let rec asm_aux acc list =
    List.fold_left
      (fun ((env, bcp, tcp, ap_delta, lits) as acc) ({F.f=f} as ff ,dep) ->
        refresh_model_handler env;
        Options.exec_thread_yield ();
        let dep = add_dep f dep in
        let dep_gamma = add_dep_of_formula f dep in
        Debug.gamma env.gamma;
        (try
           let _, ex_nf, _, _ = MF.find (F.mk_not f) env.gamma in
           Options.tool_req 2 "TR-Sat-Conflict-1";
           if Options.profiling() then Profiling.bool_conflict ();
           raise (IUnsat (Ex.union dep_gamma ex_nf, Th.cl_extract env.tbox))
         with Not_found -> ());
        if MF.mem f env.gamma then begin
	  Options.tool_req 2 "TR-Sat-Remove";
          acc
        end
        else
	  let env =
	    if ff.F.mf && greedy () then
              { env with inst=
		  Inst.add_terms env.inst (F.ground_terms_rec f) ff }
            else env
          in
	  Debug.assume ff dep env;
	  let env =
            { env with
              gamma = MF.add f (ff,dep_gamma,env.dlevel,env.plevel) env.gamma;
              plevel = env.plevel + 1 }
          in
	  match F.view f with
	    | F.Unit (f1, f2) ->
	      Options.tool_req 2 "TR-Sat-Assume-U";
              let lst = [{ff with F.f=f1},dep ; {ff with F.f=f2},dep] in
	      asm_aux (env, true, tcp, ap_delta, lits) lst
	    | F.Clause(f1,f2) ->
	      Options.tool_req 2 "TR-Sat-Assume-C";
	      let p1 = {ff with F.f=f1} in
	      let p2 = {ff with F.f=f2} in
              let p1, p2 =
                if F.size f1 <= F.size f2 then p1, p2 else p2, p1 in
	      env, true, tcp, (p1,p2,dep)::ap_delta, lits

	    | F.Lemma l ->
	      Options.tool_req 2 "TR-Sat-Assume-Ax";
              let env = {env with inst = Inst.add_lemma env.inst ff dep} in
              env, true, tcp, ap_delta, lits

	    | F.Literal a ->(*
	      Options.tool_req 2 "TR-Sat-Assume-Lit";
	      let env =
	        if ff.F.mf then
                  {env with inst =
                      Inst.add_terms env.inst (A.LT.terms_nonrec a) ff}
	        else env
	      in
	      let tbox, new_terms, cpt =
                try Th.assume [a, dep, env.dlevel, env.plevel] env.tbox
                with Exception.Inconsistent _ as e ->
                  if Options.profiling() then Profiling.theory_conflict();
                  raise e
              in
	      let inst = Inst.add_terms env.inst new_terms ff in
	      let env = { env with tbox = tbox; inst = inst } in
	      env, true, true, ap_delta*)
              let lits = (a, ff, dep, env.dlevel, env.plevel)::lits in
              let acc = env, true, true, ap_delta, lits in
              acc

	    | F.Skolem quantif ->
	      Options.tool_req 2 "TR-Sat-Assume-Sko";
	      let f' = F.skolemize quantif  in
	      asm_aux (env, true, tcp, ap_delta, lits) [{ff with F.f=f'},dep]

            | F.Let {F.let_var=lvar; let_term=lterm; let_subst=s; let_f=lf} ->
	      Options.tool_req 2 "TR-Sat-Assume-Let";
              let f' = F.apply_subst s lf in
	      let id = F.id f' in
              let v = Symbols.Map.find lvar (fst s) in
              let lst = [{ff with F.f=F.mk_lit (A.LT.mk_eq v lterm) id}, dep;
                         {ff with F.f=f'}, dep] in
              asm_aux (env, true, tcp, ap_delta, lits) lst
      ) acc list

  let profile_conflicting_instances exp =
    if Options.profiling() then
      SF.iter
        (fun f ->
          match F.view f with
          | F.Lemma {F.name; loc} ->
            Profiling.conflicting_instance name loc
          | _ -> ()
        )(Ex.formulas_of exp)

  let rec assume env list =
    if list = [] then env
    else
      try
        let result = asm_aux (env, false, false, [], []) list in
        let env, list = propagations result in
        assume env list
      with Exception.Inconsistent (expl, classes) ->
        profile_conflicting_instances expl;
        Debug.inconsistent expl env;
        Options.tool_req 2 "TR-Sat-Conflict-2";
        env.heuristics := Heuristics.bump_activity !(env.heuristics) expl;
        raise (IUnsat (expl, classes))


  let new_inst_level env =
    let new_ilevel = env.ilevel + 1 in
    let env = {env with ilevel = new_ilevel} in
    if Options.profiling() then Profiling.instantiation new_ilevel;
    Debug.instantiate env;
    env

  let instantiate_ground_preds env =
    MF.fold
      (fun f _ acc ->
        match F.view f with
        | F.Literal a ->
          (match Literal.LT.view a with
          | Literal.Pred(p, is_neg) ->
            if Term.Map.mem p env.ground_preds then begin
              let ff, pred_name, loc = Term.Map.find p env.ground_preds in
              if MF.mem ff.F.f env.gamma then acc
              else begin
                if Options.profiling() then
                  Profiling.new_instance_of pred_name loc true;
                (ff, Ex.empty) :: acc
              end
            end
                else acc
          | _ -> acc)
        | _ -> acc
      )env.gamma []

  let rec unsat_rec env fg =
    try back_tracking (assume env [fg])
    with IUnsat (d, classes) ->
      Debug.bottom classes;
      Debug.unsat ();
      d

  and try_greedy env =
    if greedy () then raise (Sat env);
    let gre_inst =
      MF.fold
        (fun f (gf,_,_,_) inst ->
          Inst.add_terms inst (F.ground_terms_rec f) gf)
        env.gamma env.inst
    in
    let env = new_inst_level env in
    let gd2, ngd2 = Inst.m_predicates gre_inst env.tbox (selector env) in
    let l2 = List.rev_append (List.rev gd2) ngd2 in
    if Options.profiling() then Profiling.instances l2;
    let env = assume env l2 in

    let gd1, ngd1 = Inst.m_lemmas gre_inst env.tbox (selector env) in

    let l1 = List.rev_append (List.rev gd1) ngd1 in
    if Options.profiling() then Profiling.instances l1;
    let env = assume env l1 in
    match l1, l2 with
    | [], [] ->
      if all_models () then
        begin
          let m = extract_prop_model env in
	  Format.printf "--- SAT ---\n";
	  Format.printf "%a@." print_prop_model m;
	  raise (IUnsat (Ex.make_deps m, []))
        end;
      raise (Sat env)
    | l1, l2 -> back_tracking env

  and back_tracking env = match env.delta with
    | [] ->
      let env = new_inst_level env in
      let gd2, ngd2 = Inst.m_predicates env.inst env.tbox (selector env) in
      let l2 = List.rev_append (List.rev gd2) ngd2 in
      if Options.profiling() then Profiling.instances l2;
      let env = assume env l2 in

      let gd1, ngd1 = Inst.m_lemmas env.inst env.tbox (selector env) in
      let l1 = List.rev_append (List.rev gd1) ngd1 in
      if Options.profiling() then Profiling.instances l1;
      let env = assume env l1 in
      begin match l1, l2 with
        | [], [] ->
	  if all_models () then
	    begin
	      let m = extract_prop_model env in
	      Format.printf "--- SAT ---\n";
	      Format.printf "%a@." print_prop_model m;
	      raise (IUnsat (Ex.make_deps m, []))
	    end;
          begin match instantiate_ground_preds env with
          | [] -> try_greedy env
          | l ->
            let env = assume env l in
            back_tracking env
          end
        | l1, l2 -> back_tracking env
      end

    | (_::_) as l ->
      let ({F.f=f} as a,b,d) , l = Heuristics.choose l !(env.heuristics) in
      let new_level = env.dlevel + 1 in
      if Options.profiling() then Profiling.decision new_level;
      let env_a =
        {env with
          delta=l;
          dlevel = new_level;
          plevel = 0}
      in
      Debug.decide f env_a;
      let dep = unsat_rec env_a (a,Ex.singleton (Ex.Bj f)) in
      Debug.unsat_rec dep;
      try
        let dep' = Ex.remove (Ex.Bj f) dep in
        Debug.backtracking f env;
        Options.tool_req 2 "TR-Sat-Decide";
        if Options.profiling() then begin
          Profiling.reset_dlevel env.dlevel;
          Profiling.reset_ilevel env.ilevel;
        end;
        unsat_rec
	  (assume {env with delta=l} [b, Ex.union d dep'])
	  ({a with F.f=F.mk_not f},dep')
      with Not_found ->
        Debug.backjumping (F.mk_not f) env;
        Options.tool_req 2 "TR-Sat-Backjumping";
        dep


  let unsat env gf =
    Debug.is_it_unsat gf;
    try
      let env = assume env [gf, Ex.empty] in
      let env =
        if not (greedy ()) then env
        else
	  {env with inst=
	      Inst.add_terms env.inst (F.ground_terms_rec gf.F.f) gf}
      in
      let env = new_inst_level env in
      let gd, ngd = Inst.m_predicates env.inst env.tbox (selector env) in
      let l = List.rev_append (List.rev gd) ngd in
      if Options.profiling() then Profiling.instances l;
      let env = assume env l in

      (* goal directed for lemmas *)
      let gd, _ = Inst.m_lemmas env.inst env.tbox (selector env) in
      if Options.profiling() then Profiling.instances gd;
      let env = assume env gd in

      back_tracking env
    with IUnsat (dep, classes) ->
      Debug.bottom classes;
      Debug.unsat ();
      dep

  let assume env fg =
    try assume env [fg,Ex.empty]
    with IUnsat (d, classes) ->
      Debug.bottom classes;
      raise (Unsat d)

  let unsat env fg =
    if Options.timers() then
      try
        Options.exec_timer_start Timers.M_Sat Timers.F_unsat;
        let env = unsat env fg in
        Options.exec_timer_pause Timers.M_Sat Timers.F_unsat;
        env
      with e ->
        Options.exec_timer_pause Timers.M_Sat Timers.F_unsat;
        raise e
    else unsat env fg

  let assume env fg =
    if Options.timers() then
      try
        Options.exec_timer_start Timers.M_Sat Timers.F_assume;
        let env = assume env fg in
        Options.exec_timer_pause Timers.M_Sat Timers.F_assume;
        env
      with e ->
        Options.exec_timer_pause Timers.M_Sat Timers.F_assume;
        raise e
    else assume env fg

  let empty () = {
    gamma = MF.empty;
    delta = [] ;
    dlevel = 0;
    plevel = 0;
    ilevel = 0;
    tbox = Th.empty ();
    unit_tbox = Th.empty ();
    inst = Inst.empty;
    heuristics = ref (Heuristics.empty ());
    ground_preds = Term.Map.empty;
    add_inst = fun _ -> true;
  }

  let empty_with_inst add_inst =
    { (empty ()) with add_inst = add_inst }

  let reset_steps () = steps := 0L
  let get_steps () = !steps
  let retrieve_used_context env dep =
    Inst.retrieve_used_context env.inst dep
end

let current = ref (module Dfs_sat : S)

let initialized = ref false

let set_current sat = current := sat

let load_current_sat () =
  match sat_plugin () with
  | "" ->
    if debug_sat () then eprintf "[Dynlink] Using Dfs-SAT solver@."

  | path ->
    if debug_sat () then
      eprintf "[Dynlink] Loading the SAT-solver in %s ...@." path;
    try
      Dynlink.loadfile path;
      if debug_sat () then  eprintf "Success !@.@."
    with
    | Dynlink.Error m1 ->
      if debug_sat() then begin
        eprintf
          "[Dynlink] Loading the SAT-solver in plugin \"%s\" failed!@."
          path;
        Format.eprintf ">> Failure message: %s@.@." (Dynlink.error_message m1);
      end;
      let prefixed_path = sprintf "%s/%s" Config.pluginsdir path in
      if debug_sat () then
        eprintf "[Dynlink] Loading the SAT-solver in %s ... with prefix %s@."
          path Config.pluginsdir;
      try
        Dynlink.loadfile prefixed_path;
        if debug_sat () then  eprintf "Success !@.@."
      with
      | Dynlink.Error m2 ->
        if not (debug_sat()) then begin
          eprintf
            "[Dynlink] Loading the SAT-solver in plugin \"%s\" failed!@."
            path;
          Format.eprintf ">> Failure message: %s@.@."
            (Dynlink.error_message m1);
        end;
        eprintf
          "[Dynlink] Trying to load the plugin from \"%s\" failed too!@."
          prefixed_path;
        Format.eprintf ">> Failure message: %s@.@." (Dynlink.error_message m2);
        exit 1

let get_current () =
  if not !initialized then
    begin
      load_current_sat ();
      initialized := true;
    end;
  !current
