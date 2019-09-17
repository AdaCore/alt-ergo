(******************************************************************************)
(*                                                                            *)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

open Options
open Format

module E = Expr
module SE = E.Set
module ME = E.Map
module Ex = Explanation


module Make (Th : Theory.S) : Sat_solver_sig.S = struct
  module Inst = Instances.Make(Th)
  module CDCL = Satml_frontend_hybrid.Make(Th)

  exception No_suitable_decision
  exception Propagate of E.gformula * Explanation.t

  let is_fact_in_CDCL cdcl f =
    match CDCL.is_true cdcl f with
    | None -> false
    | Some (ex,lvl) ->
      assert (lvl <> 0 || Ex.has_no_bj (Lazy.force ex));
      lvl = 0

  module Heuristics = struct

    type t =
      {
        mp : float ME.t;

        (* valeur de l'increment pour l'activite des variables *)
        var_inc : float;

        (* inverse du facteur d'acitivte des vars, vaut 1/0.999 par defaut *)
        var_decay : float;
      }

    let empty () =
      {
        mp = ME.empty;
        var_inc = 1.;
        var_decay = 1. /. 0.95;
      }

    let bump_activity ({ mp; var_inc; _ } as env) expl =
      let stable = ref true in
      let mp =
        SE.fold
          (fun f mp ->
             let w = var_inc +. try ME.find f mp with Not_found -> 0. in
             stable := !stable && Pervasives.(<=) w 1e100;
             ME.add f w mp
          )(Ex.bj_formulas_of expl) mp
      in
      let mp =
        if !stable then  mp
        else ME.fold (fun f w acc -> ME.add f (w *. 1e-100) acc) mp ME.empty
      in
      { env with mp = mp; var_inc = var_inc *. env.var_decay }

    let choose delta env cdcl =
      let dec, no_dec =
        if Options.no_decisions_on__is_empty () then delta, []
        else
          List.partition
            (fun (a, _,_,_) -> Options.can_decide_on a.E.origin_name) delta
      in
      let dec =
        List.rev_map
          (fun ((a,b,_,_) as e) ->
             if Options.tableaux_cdcl () && is_fact_in_CDCL cdcl a.E.ff then
               raise (Propagate (a, Ex.empty));
             if Options.tableaux_cdcl () && is_fact_in_CDCL cdcl b.E.ff then
               raise (Propagate (b, Ex.empty));
             e, (try (ME.find a.E.ff env.mp) with Not_found -> 0.), a.E.gf
          ) dec
      in

      if Options.tableaux_cdcl () then
        (* force propagate modulo satML *)
        List.iter
          (fun (a, b, _, _) ->
             match CDCL.is_true cdcl a.E.ff with
             | Some (ex, _lvl) -> raise (Propagate (a, Lazy.force ex))
             | None ->
               match CDCL.is_true cdcl b.E.ff with
               | Some (ex, _lvl) -> raise (Propagate (b, Lazy.force ex))
               | None -> ()
          )no_dec;

      let dec =
        List.fast_sort
          (fun (_, x1, b1) (_, x2, b2) ->
             let c = Pervasives.compare b2 b1 in
             if c <> 0 then c
             else Pervasives.compare x2 x1
          )dec
      in
      (*
      match l with
      | [] -> assert false
    *)
      match dec with
      | [] -> raise No_suitable_decision
      | (e, _, _) :: r ->
        let delta =
          List.fold_left (fun acc (e, _, _) -> e :: acc) no_dec (List.rev r)
        in
        e, delta

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
    gamma : (E.gformula * Ex.t * int * int) ME.t;
    nb_related_to_goal : int;
    nb_related_to_hypo : int;
    nb_related_to_both : int;
    nb_unrelated : int;
    cdcl : CDCL.t ref;
    tcp_cache : Th_util.answer ME.t;
    delta : (E.gformula * E.gformula * Ex.t * bool) list;
    decisions : int ME.t;
    dlevel : int;
    plevel : int;
    ilevel : int;
    tbox : Th.t;
    unit_tbox : Th.t; (* theory env of facts at level 0 *)
    inst : Inst.t;
    heuristics : Heuristics.t ref;
    model_gen_mode : bool ref;
    ground_preds : (E.t * Explanation.t) ME.t; (* key <-> f *)
    add_inst: E.t -> bool;
    unit_facts_cache : (E.gformula * Ex.t) ME.t ref;
  }

  let all_models_sat_env = ref None
  let latest_saved_env = ref None
  let terminated_normally = ref false


  exception Sat of t
  exception Unsat of Ex.t
  exception I_dont_know of t
  exception IUnsat of Ex.t * SE.t list


  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct


    let print_nb_related env =
      if verbose () then begin
        fprintf fmt "----------------------------------------------------@.";
        fprintf fmt " nb_related_to_both = %d@." env.nb_related_to_both;
        fprintf fmt " nb_related_to_goal = %d@." env.nb_related_to_goal;
        fprintf fmt " nb_related_to_hypo = %d@." env.nb_related_to_hypo;
        fprintf fmt " nb_unrelated       = %d@." env.nb_unrelated;
        fprintf fmt "----------------------------------------------------@.@.";
      end

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
          match E.form_view gf.E.ff with
          | E.Not_a_form -> assert false
          | E.Lemma _   -> "lemma"
          | E.Clause _  -> "clause"
          | E.Unit _    -> "conjunction"
          | E.Skolem _  -> "skolem"
          | E.Literal _ -> "literal"
          | E.Iff _ -> "iff"
          | E.Xor _ -> "xor"
          | E.Let _ -> "let"
        in
        fprintf fmt "[sat] the following %s is unsat ? :@.%a@.@."
          s E.print gf.E.ff

    let pred_def f =
      if debug_sat () then
        eprintf "[sat] I assume a predicate: %a@.@." E.print f

    let unsat_rec dep =
      if debug_sat () then fprintf fmt "unsat_rec : %a@." Ex.print dep

    let assume gf dep env =
      if debug_sat () then
        let { E.ff = f; lem; from_terms = terms; _ } = gf in
        fprintf fmt "[sat] at level (%d, %d) I assume a " env.dlevel env.plevel;
        begin match E.form_view f with
          | E.Not_a_form -> assert false
          | E.Literal a ->
            E.print_list str_formatter terms;
            let s = flush_str_formatter () in
            let n = match lem with
              | None -> ""
              | Some ff ->
                (match E.form_view ff with
                 | E.Lemma xx -> xx.E.name
                 | E.Unit _ | E.Clause _ | E.Literal _ | E.Skolem _
                 | E.Let _ | E.Iff _ | E.Xor _ -> ""
                 | E.Not_a_form -> assert false)
            in
            fprintf fmt "LITERAL (%s : %s) %a@." n s E.print a;
            fprintf fmt "==========================================@.@."

          | E.Unit _   -> fprintf fmt "conjunction@."
          | E.Clause _ -> fprintf fmt "clause %a@." E.print f
          | E.Lemma _  -> fprintf fmt "%d-atom lemma \"%a\"@."
                            (E.size f) E.print f
          | E.Skolem _ -> fprintf fmt "skolem %a@." E.print f
          | E.Let _ -> fprintf fmt "let-in %a@." E.print f
          | E.Iff _ ->  fprintf fmt "equivalence %a@." E.print f
          | E.Xor _ ->  fprintf fmt "neg-equivalence/xor %a@." E.print f
        end;
        if verbose () then
          fprintf fmt "with explanations : %a@." Explanation.print dep

    let unsat () =
      if debug_sat () then fprintf fmt "[sat] unsat@."

    let decide f env =
      if debug_sat () then
        fprintf fmt "[sat] I decide: at level (%d, %d), on %a@."
          env.dlevel env.plevel E.print f

    let instantiate env =
      if debug_sat () then
        fprintf fmt "[sat] I instantiate at level (%d, %d). Inst level = %d@."
          env.dlevel env.plevel env.ilevel

    let backtracking f env =
      if debug_sat () then
        fprintf fmt "[sat] backtrack: at level (%d, %d), and assume not %a@."
          env.dlevel env.plevel E.print f

    let backjumping f env =
      if debug_sat () then
        fprintf fmt
          "[sat] backjump: at level (%d, %d), I ignore the case %a@."
          env.dlevel env.plevel E.print f

    let elim _ _ =
      if debug_sat () && verbose () then fprintf fmt "[sat] elim@."

    let red _ _ =
      if debug_sat () && verbose () then fprintf fmt "[sat] red@."

    (* unused --
       let delta d =
       if debug_sat () && verbose () && false then begin
        fprintf fmt "[sat] - Delta ---------------------@.";
        List.iter (fun (f1, f2, ex) ->
            fprintf fmt "(%a or %a), %a@."
              E.print f1.E.ff E.print f2.E.ff Ex.print ex) d;
        fprintf fmt "[sat] --------------------- Delta -@."
       end
    *)

    let gamma g =
      if false && debug_sat () && verbose () then begin
        fprintf fmt "[sat] --- GAMMA ---------------------@.";
        ME.iter (fun f (_, ex, dlvl, plvl) ->
            fprintf fmt  "(%d, %d) %a \t->\t%a@."
              dlvl plvl E.print f Ex.print ex) g;
        fprintf fmt "[sat] - / GAMMA ---------------------@.";
      end

    let bottom classes =
      if bottom_classes () then
        printf "bottom:%a\n@." E.print_tagged_classes classes

    let inconsistent expl env =
      if debug_sat () then
        fprintf fmt "inconsistent at level (%d, %d), reason : %a@."
          env.dlevel env.plevel Ex.print expl

    let in_mk_theories_instances () =
      if Options.debug_fpa() > 0 || debug_sat() then
        fprintf fmt "@.[sat] entering mk_theories_instances:@."

    let out_mk_theories_instances normal_exit =
      if Options.debug_fpa() > 0 || debug_sat() then
        if normal_exit then
          fprintf fmt "@.[sat] normal exit of mk_theories_instances.@.@."
        else
          fprintf fmt "@.[sat] exit mk_theories_instances with Inconsist.@.@."

    let print_f_conj fmt hyp =
      match hyp with
      | [] -> fprintf fmt "True";
      | e::l ->
        fprintf fmt "%a" E.print e;
        List.iter (fun f -> fprintf fmt " /\\  %a" E.print f) l

    let print_theory_instance hyp gf =
      if Options.debug_fpa() > 1 || Options.debug_sat() then begin
        fprintf fmt "@.%s >@." (E.name_of_lemma_opt gf.E.lem);
        fprintf fmt "  hypotheses: %a@." print_f_conj hyp;
        fprintf fmt "  conclusion: %a@." E.print gf.E.ff;
      end

  end
  (*BISECT-IGNORE-END*)

  let selector env f orig =
    not (ME.mem f env.gamma)
    && begin match E.form_view orig with
      | E.Lemma _ -> env.add_inst orig
      | E.Unit _ | E.Clause _ | E.Literal _ | E.Skolem _
      | E.Let _ | E.Iff _ | E.Xor _ -> true
      | E.Not_a_form -> assert false
    end

  let inst_predicates mconf env inst tbox selector ilvl =
    try Inst.m_predicates mconf inst tbox selector ilvl
    with Ex.Inconsistent (expl, classes) ->
      Debug.inconsistent expl env;
      Options.tool_req 2 "TR-Sat-Conflict-2";
      env.heuristics := Heuristics.bump_activity !(env.heuristics) expl;
      raise (IUnsat (expl, classes))

  let inst_lemmas mconf env inst tbox selector ilvl =
    try Inst.m_lemmas mconf inst tbox selector ilvl
    with Ex.Inconsistent (expl, classes) ->
      Debug.inconsistent expl env;
      Options.tool_req 2 "TR-Sat-Conflict-2";
      env.heuristics := Heuristics.bump_activity !(env.heuristics) expl;
      raise (IUnsat (expl, classes))

  let is_literal f =
    match E.form_view f with
    | E.Literal _ -> true
    | E.Unit _ | E.Clause _ | E.Lemma _ | E.Skolem _
    | E.Let _ | E.Iff _ | E.Xor _ -> false
    | E.Not_a_form -> assert false

  let extract_prop_model t =
    let s = ref SE.empty in
    ME.iter
      (fun f _ ->
         if (complete_model () && is_literal f) || E.is_in_model f then
           s := SE.add f !s
      )
      t.gamma;
    !s

  let print_prop_model fmt s =
    SE.iter (fprintf fmt "\n %a" E.print) s

  let print_model ~header fmt t =
    Format.print_flush ();
    if header then fprintf fmt "\nModel\n@.";
    let pm = extract_prop_model t in
    if not (SE.is_empty pm) then begin
      fprintf fmt "Propositional:";
      print_prop_model fmt pm;
      fprintf fmt "\n@.";
    end;
    Th.print_model fmt t.tbox


  let refresh_model_handler =
    if model () then
      fun t ->
        try
          let alrm =
            if Options.get_is_gui() then
              Sys.sigalrm (* troubles with GUI+VTARLM *)
            else
              Sys.sigvtalrm
          in
          Sys.set_signal alrm
            (Sys.Signal_handle (fun _ ->
                 printf "%a@." (print_model ~header:true) t;
                 Options.exec_timeout ()))
        with Invalid_argument _ -> ()
    else fun _ -> ()

  (* sat-solver *)

  let mk_gf f name mf gf =
    { E.ff = f;
      origin_name = name;
      gdist = -1;
      hdist = -1;
      nb_reductions = 0;
      trigger_depth = max_int;
      age= 0;
      lem= None;
      from_terms = [];
      mf= mf;
      gf= gf;
      theory_elim = true; }


  (* hybrid functions*)
  let print_decisions_in_the_sats msg env =
    if Options.tableaux_cdcl () && verbose() then begin
      fprintf fmt "-----------------------------------------------------@.";
      fprintf fmt ">> %s@." msg;
      fprintf fmt "decisions in DfsSAT are:@.";
      let l = ME.bindings env.decisions in
      let l = List.fast_sort (fun (_,i) (_,j) -> j - i) l in
      List.iter
        (fun (f, i) ->
           fprintf fmt "%d  -> %a@." i E.print f
        )l;
      fprintf fmt "decisions in satML are:@.";
      List.iter
        (fun (i, f) ->
           fprintf fmt "%d  -> %a@." i E.print f
        )(CDCL.get_decisions !(env.cdcl));
      fprintf fmt "-----------------------------------------------------@."
    end

  let cdcl_same_decisions env =
    if Options.tableaux_cdcl () && enable_assertions () then begin
      let cdcl_decs = CDCL.get_decisions !(env.cdcl) in
      let ok = ref true in
      let decs =
        List.fold_left
          (fun decs (i, d) ->
             try
               let j = ME.find d decs in
               assert (i = j);
               ME.remove d decs
             with Not_found ->
               ok := false;
               fprintf fmt "@.Aie! decision %a is only in satML !!@.@."
                 E.print d;
               fprintf fmt "nb decisions in DfsSAT: %d@."
                 (ME.cardinal env.decisions);
               fprintf fmt "nb decisions in satML:  %d@."
                 (List.length cdcl_decs);
               decs
          )env.decisions cdcl_decs
      in
      if decs != ME.empty then begin
        fprintf fmt "Aie ! some decisions only in DfsSAT@.";
        ok := false;
      end;
      !ok
    end
    else true

  let cdcl_known_decisions ex env =
    Ex.fold_atoms
      (fun e b ->
         match e with
         | Ex.Bj f -> b && ME.mem f env.decisions
         | _ -> b
      )ex true

  let shift gamma ex acc0 =
    let l =
      Ex.fold_atoms
        (fun e acc ->
           match e with
           | Ex.Bj f ->
             let dec =
               try let _,_,dec,_ = ME.find f gamma in dec
               with Not_found -> max_int
             in
             (f, dec) :: acc
           | _ ->
             acc
        )ex []
    in
    (* try to keep the decision ordering *)
    let l = List.fast_sort (fun (_,i) (_,j) -> j - i) l in
    List.fold_left (fun acc (f, _) -> E.mk_imp f acc (E.id f)) acc0 l


  let cdcl_assume delay env l =
    if debug_sat() && verbose() then fprintf fmt "[fun_cdcl_assume]@.";
    let gamma = env.gamma in
    try
      let l =
        List.rev_map
          (fun ((gf, ex) as e) ->
             if Ex.has_no_bj ex then e
             else {gf with E.ff = shift gamma ex gf.E.ff}, Ex.empty
          )(List.rev l)
      in
      env.cdcl := CDCL.assume delay !(env.cdcl) l
    with
    | CDCL.Bottom (ex, l, cdcl) ->
      if debug_sat() &&  verbose() then
        fprintf fmt "[fun_cdcl_assume] conflict@.";
      env.cdcl := cdcl;
      assert (cdcl_known_decisions ex env);
      raise (IUnsat(ex, l))

  let cdcl_decide env f dlvl =
    if debug_sat() &&  verbose() then fprintf fmt "[fun_cdcl_decide]@.";
    try
      env.cdcl := CDCL.decide !(env.cdcl) f dlvl
    with
    | CDCL.Bottom (ex, l, _cdcl) ->
      if debug_sat() && verbose() then
        fprintf fmt "[fun_cdcl_decide] conflict@.";
      assert (cdcl_known_decisions ex env);
      (* no need to save cdcl here *)
      raise (IUnsat(ex, l))
    | e ->
      fprintf fmt "%s@." (Printexc.to_string e);
      assert false

  let cdcl_forget_decision env f lvl =
    try
      env.cdcl := CDCL.forget_decision !(env.cdcl) f lvl
    with
    | _ ->
      fprintf fmt "@.cdcl_backjump error:@.%s@.@." (Printexc.get_backtrace ());
      assert false

  let cdcl_learn_clause delay env ex acc0 =
    let f = shift env.gamma ex acc0 in
    let ff = mk_gf f "<cdcl_learn_clause>" true true in
    cdcl_assume delay env [ff, Ex.empty]

  let profile_conflicting_instances exp =
    if Options.profiling() then
      SE.iter
        (fun f ->
           match E.form_view f with
           | E.Lemma { E.name; loc; _ } ->
             Profiling.conflicting_instance name loc
           | E.Unit _ | E.Clause _ | E.Literal _ | E.Skolem _
           | E.Let _ | E.Iff _ | E.Xor _ -> ()
           | E.Not_a_form -> assert false
        )(Ex.formulas_of exp)

  let do_case_split env origin =
    if Options.case_split_policy () == origin then
      try
        if debug_sat() then fprintf fmt "[sat] performing case-split@.";
        let tbox, new_terms = Th.do_case_split env.tbox in
        let inst =
          Inst.add_terms env.inst new_terms (mk_gf E.vrai "" false false) in
        {env with tbox = tbox; inst = inst}
      with Ex.Inconsistent (expl, classes) ->
        Debug.inconsistent expl env;
        Options.tool_req 2 "TR-Sat-Conflict-2";
        env.heuristics := Heuristics.bump_activity !(env.heuristics) expl;
        raise (IUnsat (expl, classes))
    else env

  let b_elim f env =
    try
      let _ = ME.find f env.gamma in
      Options.tool_req 2 "TR-Sat-Bcp-Elim-1";
      if Options.profiling() then Profiling.elim true;
      true
    with Not_found -> false


  let update_unit_facts env ff dep =
    let f = ff.E.ff in
    if sat_learning () && not (ME.mem f !(env.unit_facts_cache)) then
      begin
        assert (Ex.has_no_bj dep);
        env.unit_facts_cache := ME.add f (ff, dep) !(env.unit_facts_cache)
      end

  let learn_clause ({ gamma; _ } as env) ff0 dep =
    if sat_learning () then
      let fl, dep =
        Ex.fold_atoms
          (fun e (l, ex) ->
             match e with
             | Ex.Bj f ->
               let d =
                 try let _,_,d,_ = ME.find f gamma in d
                 with Not_found -> max_int
               in
               (E.neg f, d) :: l, ex
             | _ -> l, Ex.add_fresh e ex
          )dep ([], Ex.empty)
      in
      let fl = List.fast_sort (fun (_, d1) (_,d2) -> d1 - d2) fl in
      let f =
        List.fold_left
          (fun acc (f, _) -> E.mk_or f acc false (E.id f))
          ff0.E.ff fl
      in
      update_unit_facts env {ff0 with E.ff=f} dep


  let query_of tcp_cache tmp_cache ff a env =
    try ME.find a !tcp_cache
    with Not_found ->
    try ME.find a !tmp_cache
    with Not_found ->
      assert (E.is_ground a);
      match Th.query a env.tbox with
      | None -> tmp_cache := ME.add a None !tmp_cache; None
      | Some (ex,_) as y ->
        if Options.tableaux_cdcl () then
          cdcl_learn_clause true env ex (ff.E.ff);
        learn_clause env ff ex;
        tcp_cache := ME.add a y !tcp_cache; y

  let th_elim tcp_cache tmp_cache ff env =
    match E.form_view ff.E.ff with
    | E.Literal a ->
      let ans = query_of tcp_cache tmp_cache ff a env in
      if ans != None then
        begin
          Options.tool_req 2 "TR-Sat-Bcp-Elim-2";
          if Options.profiling() then Profiling.elim false;
        end;
      ans
    | E.Unit _ | E.Clause _ | E.Lemma _ | E.Skolem _
    | E.Let _ | E.Iff _ | E.Xor _ -> None
    | E.Not_a_form -> assert false

  let red tcp_cache tmp_cache ff env tcp =
    let nf = E.neg ff.E.ff in
    let nff = {ff with E.ff = nf} in
    try
      let _, ex = ME.find nf !(env.unit_facts_cache) in
      Some(ex, []), true
    with Not_found ->
    try
      let _, ex, _, _ = ME.find nf env.gamma in
      let r = Some (ex, Th.cl_extract env.tbox) in
      Options.tool_req 2 "TR-Sat-Bcp-Red-1";
      r, true
    with Not_found ->
      if not tcp then None, false
      else match E.form_view nf with
        | E.Literal a ->
          let ans = query_of tcp_cache tmp_cache nff a env in
          if ans != None then Options.tool_req 2 "TR-Sat-Bcp-Red-2";
          ans, false
        | E.Unit _ | E.Clause _ | E.Lemma _ | E.Skolem _
        | E.Let _ | E.Iff _ | E.Xor _ -> None, false
        | E.Not_a_form -> assert false

  let red tcp_cache tmp_cache ff env tcp =
    match red tcp_cache tmp_cache ff env tcp with
    | (Some _, _)  as ans -> ans
    | None, b ->
      if not (Options.tableaux_cdcl ()) then
        None, b
      else
        match CDCL.is_true !(env.cdcl) (E.neg ff.E.ff) with
        | Some (ex, _lvl) ->
          let ex = Lazy.force ex in
          if debug_sat() && verbose() then
            fprintf fmt "red thanks to satML@.";
          assert (cdcl_known_decisions ex env);
          Some(ex, []), true
        | None ->
          None, b

  let add_dep f dep =
    match E.form_view f with
    | E.Literal _ ->
      if not (unsat_core ()) || Ex.mem (Ex.Bj f) dep then dep
      else Ex.union (Ex.singleton (Ex.Dep f)) dep
    | E.Clause _ ->
      if unsat_core () then Ex.union (Ex.singleton (Ex.Dep f)) dep
      else dep
    | E.Unit _ | E.Lemma _ | E.Skolem _ | E.Let _ | E.Iff _ | E.Xor _ -> dep
    | E.Not_a_form -> assert false

  let rec add_dep_of_formula f dep =
    let dep = add_dep f dep in
    match E.form_view f with
    | E.Unit (f1, f2) ->
      if not (unsat_core ()) then dep
      else add_dep_of_formula f2 (add_dep_of_formula f1 dep)
    | E.Lemma _ | E.Clause _ | E.Literal _ | E.Skolem _
    | E.Let _ | E.Iff _ | E.Xor _ -> dep
    | E.Not_a_form -> assert false

  (* currently:
     => this is not done modulo theories
     => unit_facts_cache not taken into account *)
  let update_distances =
    let aux gf ff =
      let gdist = max ff.E.gdist gf.E.gdist in
      let hdist = max ff.E.hdist gf.E.hdist in
      let gdist = if gdist < 0 then gdist else gdist + 1 in
      let hdist = if hdist < 0 then hdist else hdist + 1 in
      {gf with E.gdist; hdist}
    in
    fun env gf red ->
      let nf = E.neg red in
      try let ff, _ = ME.find nf !(env.unit_facts_cache) in aux gf ff
      with Not_found ->
      try let ff, _, _, _ = ME.find nf env.gamma in aux gf ff
      with Not_found -> gf



  let do_bcp env tcp tcp_cache tmp_cache delta acc =
    let tcp = tcp && not (Options.no_tcp ()) in
    List.fold_left
      (fun (cl,u)
        ((({ E.ff = f1; _ } as gf1), ({ E.ff = f2; _ } as gf2), d, _) as fd) ->
        Debug.elim gf1 gf2;
        if b_elim f1 env || b_elim f2 env then (cl,u)
        else
          try
            if not tcp then raise Exit;
            assert (gf1.E.theory_elim == gf2.E.theory_elim);
            let u =
              match th_elim tcp_cache tmp_cache gf1 env,
                    th_elim tcp_cache tmp_cache gf2 env with
              | None, None -> raise Exit
              | Some _, _ | _, Some _ when gf1.E.theory_elim -> u

              | Some _, Some _ ->
                u (* eliminate if both are true ? why ? *)
              (*(gf1, Ex.union d d1) :: (gf2, Ex.union d d2) :: u*)

              | Some (d1, _), _ -> (gf1, Ex.union d d1) :: u

              | _, Some (d2, _) -> (gf2, Ex.union d d2) :: u
            in
            cl, u
          with Exit ->
            begin
              Debug.red gf1 gf2;
              match
                red tcp_cache tmp_cache gf1 env tcp,
                red tcp_cache tmp_cache gf2 env tcp
              with
              | (Some (d1, c1), b1) , (Some (d2, c2), b2) ->
                if Options.profiling() then Profiling.bcp_conflict b1 b2;
                let expl = Ex.union (Ex.union d d1) d2 in
                let c = List.rev_append c1 c2 in
                raise (Ex.Inconsistent (expl, c))

              | (Some(d1, _), b) , (None, _) ->
                if Options.profiling() then Profiling.red b;
                let gf2 =
                  {gf2 with E.nb_reductions = gf2.E.nb_reductions + 1} in
                let gf2 = update_distances env gf2 f1 in
                cl, (gf2,Ex.union d d1) :: u

              | (None, _) , (Some(d2, _),b) ->
                if Options.profiling() then Profiling.red b;
                let gf1 =
                  {gf1 with E.nb_reductions = gf1.E.nb_reductions + 1} in
                let gf1 = update_distances env gf1 f2 in
                cl, (gf1,Ex.union d d2) :: u

              | (None, _) , (None, _) -> fd::cl , u
            end
      ) acc delta


  let theory_assume env facts =
    Options.tool_req 2 "TR-Sat-Assume-Lit";
    if facts == [] then env
    else
      let facts, ufacts, inst, mf, gf =
        List.fold_left
          (fun (facts, ufacts, inst, mf, gf) (a, ff, ex, dlvl, plvl) ->
             if not (E.is_ground a) then begin
               fprintf fmt "%a is not ground@." E.print a;
               assert false
             end;
             let facts = (a, ex, dlvl, plvl) :: facts in
             let ufacts =
               if Ex.has_no_bj ex then (a, ex, dlvl, plvl) :: ufacts
               else ufacts
             in
             if not ff.E.mf then begin
               fprintf fmt "%a@." E.print ff.E.ff;
               assert false
             end;
             let inst =
               if ff.E.mf then Inst.add_terms inst (E.max_terms_of_lit a) ff
               else inst
             in
             facts, ufacts, inst, mf || ff.E.mf, gf || ff.E.gf
          )([], [], env.inst, false, false) facts
      in
      let utbox, _, _ = (* assume unit facts in the theory *)
        if ufacts != [] && env.dlevel > 0 then
          try Th.assume ~ordered:false ufacts env.unit_tbox
          with Ex.Inconsistent (reason, _) as e ->
            assert (Ex.has_no_bj reason);
            if Options.profiling() then Profiling.theory_conflict();
            if debug_sat() then fprintf fmt "[sat] solved by unit_tbox@.";
            raise e
        else env.unit_tbox, SE.empty, 0
      in
      let tbox, new_terms, cpt =
        try Th.assume facts env.tbox
        with Ex.Inconsistent _ as e ->
          if Options.profiling() then Profiling.theory_conflict();
          raise e
      in
      let utbox = if env.dlevel = 0 then tbox else utbox in
      let inst = Inst.add_terms inst new_terms (mk_gf E.vrai "" mf gf) in
      Options.incr_and_check_steps cpt;
      { env with tbox = tbox; unit_tbox = utbox; inst = inst }

  let propagations ((env, bcp, tcp, ap_delta, lits) as result) =
    let env = theory_assume env lits in
    let env = do_case_split env Util.AfterTheoryAssume in
    Debug.propagations result;
    let tcp_cache = ref env.tcp_cache in
    let tmp_cache = ref ME.empty in
    let acc =
      if bcp then do_bcp env tcp tcp_cache tmp_cache env.delta ([], [])
      else env.delta, [] (* no even bcp for old clauses *)
    in
    (*both bcp and tcp set to true for new clauses*)
    let delta, unit = do_bcp env true tcp_cache tmp_cache ap_delta acc in
    {env with delta = delta; tcp_cache = !tcp_cache}, unit

  let update_nb_related t ff =
    let gdist = ff.E.gdist in
    let hdist = ff.E.hdist in
    match gdist >= 0, hdist >= 0 with
    | true , false -> {t with nb_related_to_goal = t.nb_related_to_goal + 1}
    | false, true  -> {t with nb_related_to_hypo = t.nb_related_to_hypo + 1}
    | false, false -> {t with nb_unrelated = t.nb_unrelated + 1}
    | true , true  ->
      (* update these three counter to simplify comparaisons
         in the rest of the module: both+1 imples goal+1 *)
      {t with
       nb_related_to_both = t.nb_related_to_both + 1;
       nb_related_to_goal = t.nb_related_to_goal + 1;
       nb_related_to_hypo = t.nb_related_to_hypo + 1}


  let rec asm_aux acc list =
    List.fold_left
      (fun
        ((env, _bcp, tcp, ap_delta, lits) as acc)
        ({ E.ff = f; _ } as ff, dep) ->
        refresh_model_handler env;
        Options.exec_thread_yield ();
        let dep = add_dep f dep in
        let dep_gamma = add_dep_of_formula f dep in
        (* propagate all unit facts to cache *)
        if sat_learning () && Ex.has_no_bj dep_gamma then
          update_unit_facts env ff dep_gamma;
        Debug.gamma env.gamma;
        (try
           let _, ex_nf, _, _ = ME.find (E.neg f) env.gamma in
           Options.tool_req 2 "TR-Sat-Conflict-1";
           if Options.profiling() then Profiling.bool_conflict ();
           let exx = Ex.union dep_gamma ex_nf in
            (*
           missing VSID, but we have regressions when it is activated
           env.heuristics := Heuristics.bump_activity !(env.heuristics) exx;*)
           raise (IUnsat (exx, Th.cl_extract env.tbox))
         with Not_found -> ());
        if ME.mem f env.gamma then begin
          Options.tool_req 2 "TR-Sat-Remove";
          acc
        end
        else
          let env =
            if ff.E.mf && greedy () then
              { env with inst=
                           Inst.add_terms
                             env.inst (E.max_ground_terms_rec_of_form f) ff }
            else env
          in
          Debug.assume ff dep env;
          let env =
            { env with
              gamma = ME.add f (ff,dep_gamma,env.dlevel,env.plevel) env.gamma;
              plevel = env.plevel + 1;
            }
          in
          let env = update_nb_related env ff in
          match E.form_view f with
          | E.Not_a_form -> assert false
          | E.Iff (f1, f2) ->
            let id = E.id f in
            let g = E.elim_iff f1 f2 id ~with_conj:true in
            if Options.tableaux_cdcl () then begin
              let f_imp_g = E.mk_imp f g id in
              (* correct to put <-> ?*)
              cdcl_assume false env [{ff with E.ff=f_imp_g}, Ex.empty]
            end;
            asm_aux (env, true, tcp, ap_delta, lits) [{ff with E.ff = g}, dep]

          | E.Xor (f1, f2) ->
            let id = E.id f in
            let g = E.elim_iff f1 f2 id ~with_conj:false |> E.neg in
            if Options.tableaux_cdcl () then begin
              let f_imp_g = E.mk_imp f g id in
              (* should do something similar for Let ? *)
              cdcl_assume false env [{ff with E.ff=f_imp_g}, Ex.empty]
            end;
            asm_aux (env, true, tcp, ap_delta, lits) [{ff with E.ff = g}, dep]

          | E.Unit (f1, f2) ->
            Options.tool_req 2 "TR-Sat-Assume-U";
            let lst = [{ff with E.ff=f1},dep ; {ff with E.ff=f2},dep] in
            asm_aux (env, true, tcp, ap_delta, lits) lst

          | E.Clause(f1,f2,is_impl) ->
            Options.tool_req 2 "TR-Sat-Assume-C";
            let p1 = {ff with E.ff=f1} in
            let p2 = {ff with E.ff=f2} in
            let p1, p2 =
              if is_impl || E.size f1 <= E.size f2 then p1, p2 else p2, p1
            in
            env, true, tcp, (p1,p2,dep,is_impl)::ap_delta, lits

          | E.Lemma _ ->
            Options.tool_req 2 "TR-Sat-Assume-Ax";
            let inst_env = Inst.add_lemma env.inst ff dep in
            if Options.tableaux_cdcl () then
              cdcl_assume false env [ff,dep];
            {env with inst = inst_env}, true, tcp, ap_delta, lits

          | E.Literal a ->
            let lits = (a, ff, dep, env.dlevel, env.plevel)::lits in
            let acc = env, true, true, ap_delta, lits in
            begin
              try (* ground preds bahave like proxies of lazy CNF *)
                let af, adep = ME.find a env.ground_preds in
                if Options.tableaux_cdcl () then
                  cdcl_assume false env
                    [{ff with E.ff = E.mk_imp f af (E.id f)}, adep];
                asm_aux acc [{ff with E.ff = af}, Ex.union dep adep]
              with Not_found -> acc
            end

          | E.Skolem quantif ->
            Options.tool_req 2 "TR-Sat-Assume-Sko";
            let f' = E.skolemize quantif  in
            if Options.tableaux_cdcl () then begin
              let f_imp_f' = E.mk_imp f f' (E.id f) in
              (* correct to put <-> ?*)
              (* should do something similar for Let ? *)
              cdcl_assume false env [{ff with E.ff=f_imp_f'}, Ex.empty]
            end;
            asm_aux (env, true, tcp, ap_delta, lits) [{ff with E.ff=f'},dep]

          | E.Let letin ->
            Options.tool_req 2 "TR-Sat-Assume-Let";
            let elim_let = E.elim_let letin in
            let ff = {ff with E.ff = elim_let} in
            if Options.tableaux_cdcl () then begin
              let f_imp_f' = E.mk_imp f elim_let (E.id f) in
              (* correct to put <-> ?*)
              (* should do something similar for Let ? *)
              cdcl_assume false env [{ff with E.ff=f_imp_f'}, Ex.empty]
            end;
            asm_aux (env, true, tcp, ap_delta, lits) [ff, dep]

      ) acc list

  let rec assume env list =
    if list == [] then
      begin
        print_decisions_in_the_sats "exit assume rec" env;
        assert (cdcl_same_decisions env);
        env
      end
    else
      try
        let result = asm_aux (env, false, false, [], []) list in
        let env, list = propagations result in
        assume env list
      with Ex.Inconsistent (expl, classes) ->
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


  (* this function has an internal state used to store the latest
     generated instances. These instances are used to try to backjump
     as far as possible using simple "assume"s, ie without decision.
     The reason for this modification is that a set of instances may
     cause several conflict, and we don't always detect the one which
     makes us backjump better. *)
  let update_instances_cache =
    let last_cache = ref [] in
    fun l_opt ->
      match l_opt with
      | None   -> Some !last_cache (* Get *)
      | Some l -> (* Set or reset if l = [] *)
        last_cache := List.filter (fun (_,e) -> Ex.has_no_bj e) l;
        None

  (* returns the (new) env and true if some new instances are made *)
  let inst_and_assume mconf env inst_function inst_env =
    let gd, ngd =
      inst_function mconf env inst_env env.tbox (selector env) env.ilevel
    in
    let l = List.rev_append (List.rev gd) ngd in

    (* do this to avoid loosing instances when a conflict is detected
       directly with some of these instances only, ie before assumign
       the others *)
    if sat_learning () then
      List.iter
        (fun (gf, dep) ->
           if Ex.has_no_bj dep then update_unit_facts env gf dep;
        )l;
    if Options.tableaux_cdcl () then
      cdcl_assume false env l;

    if Options.profiling() then Profiling.instances l;
    match l with
    | [] -> env, false
    | _  ->
      (* Put new generated instances in cache *)
      ignore (update_instances_cache (Some l));
      if Options.tableaux_cdcl () then
        cdcl_assume false env l;
      let env = assume env l in
      (* No conflict by direct assume, empty cache *)
      ignore (update_instances_cache (Some []));
      env, true

  let update_all_models_option env =
    if all_models () then
      begin
        (* should be used when all_models () is activated only *)
        if !all_models_sat_env == None then all_models_sat_env := Some env;
        let m =
          ME.fold
            (fun f _ s -> if is_literal f then SE.add f s else s)
            env.gamma SE.empty
        in
        Format.printf "--- SAT model found ---";
        Format.printf "%a@." print_prop_model m;
        Format.printf "--- / SAT model  ---@.";
        raise (IUnsat (Ex.make_deps m, []))
      end

  let get_all_models_answer () =
    if all_models () then
      match !all_models_sat_env with
      | Some env -> raise (I_dont_know env)
      | None -> fprintf fmt "[all-models] No SAT models found@."


  let compute_concrete_model env origin =
    if abs (interpretation ()) <> origin then env
    else
      try
        (* to push pending stuff *)
        let env = do_case_split env (Options.case_split_policy ()) in
        let env = {env with tbox = Th.compute_concrete_model env.tbox} in
        latest_saved_env := Some env;
        env
      with Ex.Inconsistent (expl, classes) ->
        Debug.inconsistent expl env;
        Options.tool_req 2 "TR-Sat-Conflict-2";
        env.heuristics := Heuristics.bump_activity !(env.heuristics) expl;
        raise (IUnsat (expl, classes))


  let return_cached_model return_function =
    let i = abs(interpretation ()) in
    assert (i = 1 || i = 2 || i = 3);
    assert (not !terminated_normally);
    terminated_normally := true; (* to avoid loops *)
    begin
      match !latest_saved_env with
      | None ->
        fprintf fmt "[FunSat] %s%s%s@."
          "It seems that no model has been computed so for."
          " You may need to change your model generation strategy"
          ", or to increase your timeout."
      | Some env ->
        let cs_tbox = Th.get_case_split_env env.tbox in
        let uf = Ccx.Main.get_union_find cs_tbox in
        Uf.output_concrete_model uf
    end;
    return_function ()


  let () =
    at_exit
      (fun () ->
         let i = abs(interpretation ()) in
         if not !terminated_normally && (i = 1 || i = 2 || i = 3) then
           return_cached_model (fun () -> ())
      )


  let return_answer env orig return_function =
    update_all_models_option env;
    let env = compute_concrete_model env orig in
    let uf = Ccx.Main.get_union_find (Th.get_case_split_env env.tbox) in
    Options.Time.unset_timeout ~is_gui:(Options.get_is_gui());
    Uf.output_concrete_model uf;
    terminated_normally := true;
    return_function env


  let switch_to_model_gen env =
    not !terminated_normally &&
    not !(env.model_gen_mode) &&
    let i = abs (interpretation ()) in
    (i = 1 || i = 2 || i = 3)


  let do_switch_to_model_gen env =
    let i = abs (interpretation ()) in
    assert (i = 1 || i = 2 || i = 3);
    if not !(env.model_gen_mode) &&
       Pervasives.(<>) (Options.interpretation_timelimit ()) 0. then
      begin
        Options.Time.unset_timeout ~is_gui:(Options.get_is_gui());
        Options.Time.set_timeout
          ~is_gui:(Options.get_is_gui())
          (Options.interpretation_timelimit ());
        env.model_gen_mode := true;
        return_answer env i (fun _ -> raise Util.Timeout)
      end
    else
      return_cached_model (fun () -> raise Util.Timeout)


  let reduce_hypotheses tcp_cache tmp_cache env acc (hyp, gf, dep) =
    Debug.print_theory_instance hyp gf;
    let dep, acc =
      List.fold_left
        (fun (dep, acc) f ->
           try
             let _, ex, _, _ = ME.find f env.gamma in
             Ex.union dep ex, acc
           with Not_found ->
           try
             (*if no_sat_learning() then raise Not_found;*)
             let _, ex = ME.find f !(env.unit_facts_cache) in
             Ex.union dep ex, ({gf with E.ff=f}, ex) :: acc
           with Not_found ->
           match E.form_view f with
           | E.Literal a ->
             begin
               match query_of tcp_cache tmp_cache {gf with E.ff=f} a env with
               | Some (ex, _) ->
                 Ex.union dep ex, ({gf with E.ff=f}, ex) :: acc
               | None ->
                 fprintf fmt "Bad inst ! Hyp %a is not true !@." E.print f;
                 assert false
             end
           | E.Unit _ | E.Clause _ | E.Lemma _ | E.Skolem _
           | E.Let _ | E.Iff _ | E.Xor _ ->
             Format.eprintf
               "Currently, arbitrary formulas in Hyps are not Th-reduced@.";
             assert false
           | E.Not_a_form ->
             assert false
        )(dep, acc) hyp
    in
    (gf, dep) :: acc

  let does_not_contain_a_disjunction =
    let rec aux f =
      match E.form_view f with
      | E.Not_a_form -> assert false
      | E.Literal _ -> true
      | E.Unit(f1, f2) -> aux f1 && aux f2
      | E.Clause _ | E.Iff _ | E.Xor _ -> false
      | E.Lemma _ | E.Skolem _ | E.Let _ ->
        (*failwith "Not in current theory axioms"*)
        false
    in
    fun (gf, _) -> aux gf.E.ff


  let mk_theories_instances ~do_syntactic_matching ~rm_clauses env inst =
    let { tbox; _ } = env in
    Debug.in_mk_theories_instances ();
    let t_match = Inst.matching_terms_info inst in
    try
      let tbox, l =
        Th.theories_instances
          ~do_syntactic_matching
          t_match tbox (selector env) env.ilevel env.dlevel
      in
      let env = {env with tbox} in
      match l with
      | [] -> env, false
      | _ ->
        let tcp_cache = ref env.tcp_cache in
        let tmp_cache = ref ME.empty in
        let rl =
          List.fold_left (reduce_hypotheses tcp_cache tmp_cache env) [] l
        in
        let l = List.rev rl in
        let l =
          if not rm_clauses then l
          else List.filter does_not_contain_a_disjunction l
        in
        let env = {env with tcp_cache = !tcp_cache} in
        ignore (update_instances_cache (Some l));
        if Options.tableaux_cdcl () then
          cdcl_assume false env l;
        let env = assume env l in
        ignore (update_instances_cache (Some []));
        Debug.out_mk_theories_instances true;
        env, l != []
    with Ex.Inconsistent (expl, classes) ->
      Debug.out_mk_theories_instances false;
      Debug.inconsistent expl env;
      Options.tool_req 2 "TR-Sat-Conflict-2";
      env.heuristics := Heuristics.bump_activity !(env.heuristics) expl;
      raise (IUnsat (expl, classes))


  let syntactic_th_inst ~rm_clauses env =
    mk_theories_instances ~do_syntactic_matching:true ~rm_clauses env

  let semantic_th_inst =
    let rec aux_rec ~rm_clauses env inst loop nb_ok =
      let env, inst_made =
        mk_theories_instances ~do_syntactic_matching:false ~rm_clauses env inst
      in
      if inst_made then incr nb_ok;
      if not inst_made || loop <= 1 then env
      else aux_rec ~rm_clauses env inst (loop - 1) nb_ok
    in
    fun ~rm_clauses env inst ~loop ->
      let nb_ok = ref 0 in
      aux_rec ~rm_clauses env inst loop nb_ok, !nb_ok > 0

  let greedy_instantiation env =
    if greedy () then return_answer env 1 (fun e -> raise (I_dont_know e));
    let gre_inst =
      ME.fold
        (fun f (gf,_,_,_) inst ->
           Inst.add_terms inst (E.max_ground_terms_rec_of_form f) gf)
        env.gamma env.inst
    in
    let env = new_inst_level env in
    let mconf =
      {Util.nb_triggers = max 10 (nb_triggers () * 10);
       no_ematching = false;
       triggers_var = true;
       use_cs = true;
       backward = Util.Normal;
       greedy = true;
      }
    in
    let env, ok1 = inst_and_assume mconf env inst_predicates gre_inst in
    let env, ok2 = inst_and_assume mconf env inst_lemmas gre_inst in
    let env, ok3 = syntactic_th_inst env gre_inst ~rm_clauses:false in
    let env, ok4 = semantic_th_inst  env gre_inst ~rm_clauses:false ~loop:4 in
    let env = do_case_split env Util.AfterMatching in
    if ok1 || ok2 || ok3 || ok4 then env
    else return_answer env 1 (fun e -> raise (I_dont_know e))

  let normal_instantiation env try_greedy =
    Debug.print_nb_related env;
    let env = do_case_split env Util.BeforeMatching in
    let env = compute_concrete_model env 2 in
    let env = new_inst_level env in
    let mconf =
      {Util.nb_triggers = nb_triggers ();
       no_ematching = no_Ematching();
       triggers_var = triggers_var ();
       use_cs = false;
       backward = Util.Normal;
       greedy = greedy ();
      }
    in
    let env, ok1 = inst_and_assume mconf env inst_predicates env.inst in
    let env, ok2 = inst_and_assume mconf env inst_lemmas env.inst in
    let env, ok3 = syntactic_th_inst env env.inst ~rm_clauses:false in
    let env, ok4 = semantic_th_inst  env env.inst ~rm_clauses:false ~loop:4 in
    let env = do_case_split env Util.AfterMatching in
    if ok1 || ok2 || ok3 || ok4 then env
    else if try_greedy then greedy_instantiation env else env


  (* should be merged with do_bcp/red/elim ?
     calls to debug hooks are missing *)
  let propagate_unit_facts_in_cache env =
    if no_sat_learning() then None
    else
      let cache = !(env.unit_facts_cache) in
      let in_cache f =
        try Some (snd (ME.find f cache))
        with Not_found -> None
      in
      let prop, delt =
        List.fold_left
          (fun (prop, new_delta) ((gf1, gf2, d, _) as e) ->
             let { E.ff = f1; _ } = gf1 in
             let { E.ff = f2; _ } = gf2 in
             let nf1 = E.neg f1 in
             let nf2 = E.neg f2 in
             match in_cache nf1, in_cache nf2 with
             | Some d1, Some d2 ->
               if Options.profiling() then Profiling.bcp_conflict true true;
               let expl = Ex.union (Ex.union d d1) d2 in
               raise (IUnsat (expl, []))

             | Some d1, _ ->
               (* a is false, so b should be true *)
               if Options.profiling() then Profiling.red true;
               let not_gf1 = {gf1 with E.ff = nf1} in
               let gf2 =
                 {gf2 with E.nb_reductions = gf2.E.nb_reductions + 1} in
               let gf2 = update_distances env gf2 f1 in
               (gf2, Ex.union d d1) :: (not_gf1, d1) :: prop, new_delta

             | _, Some d2 ->
               (* b is false, so a should be true *)
               let not_gf2 = {gf2 with E.ff = nf2} in
               let gf1 =
                 {gf1 with E.nb_reductions = gf1.E.nb_reductions + 1} in
               let gf1 = update_distances env gf1 f2 in
               (gf1, Ex.union d d2) :: (not_gf2, d2) :: prop, new_delta

             | None, None ->
               match in_cache f1, in_cache f2 with
               | None, None     -> prop, e :: new_delta
               | Some d1, _    -> (gf1, d1) :: prop, new_delta
               | None, Some d2 -> (gf2, d2) :: prop, new_delta
          )([], []) env.delta
      in
      match prop with [] -> None | _ -> Some (prop, delt)

  let rec unsat_rec env fg is_decision =
    try
      if is_decision then
        begin
          let f = (fst fg).E.ff in
          if Options.tableaux_cdcl () then
            try cdcl_decide env f (ME.find f env.decisions)
            with Not_found -> assert false
        end;
      let env = assume env [fg] in
      let env =
        if is_decision || not (Options.instantiate_after_backjump ()) then env
        else normal_instantiation env false
      in
      back_tracking env
    with
    | IUnsat (d, classes) ->
      profile_conflicting_instances d;
      Debug.bottom classes;
      Debug.unsat ();
      d

  and back_tracking env =
    try
      let env = compute_concrete_model env 3 in
      if env.delta == [] || Options.no_decisions() then
        back_tracking (normal_instantiation env true)
      else
        match propagate_unit_facts_in_cache env with
        | Some (propag, new_delta_rev) ->
          let env = {env with delta = List.rev new_delta_rev} in
          back_tracking (assume env propag)
        | None ->
          try make_one_decision env
          with No_suitable_decision ->
            back_tracking (normal_instantiation env true)
    with
    | Util.Timeout when switch_to_model_gen env -> do_switch_to_model_gen env

  and make_one_decision env =
    try
      let ({ E.ff = f; _ } as a,b,d,_is_impl), l =
        Heuristics.choose env.delta !(env.heuristics) !(env.cdcl)
      in
      let new_level = env.dlevel + 1 in
      if Options.profiling() then
        Profiling.decision new_level a.E.origin_name;
      (*fprintf fmt "@.BEFORE DECIDING %a@." E.print f;*)
      assert (cdcl_same_decisions env);
      let env_a =
        {env with
         delta=l;
         dlevel = new_level;
         plevel = 0;
         decisions = ME.add f new_level env.decisions}
      in
      if Options.tableaux_cdcl () then begin
        assert (not (is_fact_in_CDCL !(env.cdcl) f));
        assert (not (is_fact_in_CDCL !(env.cdcl) (E.neg f)));
      end;
      Debug.decide f env_a;
      let dep = unsat_rec env_a (a,Ex.singleton (Ex.Bj f)) true in
      if Options.tableaux_cdcl () then
        cdcl_forget_decision env f new_level;
      Debug.unsat_rec dep;
      try
        let dep' =
          try Ex.remove (Ex.Bj f) dep
          with Not_found when Options.no_backjumping() -> dep
        in
        Debug.backtracking f env;
        Options.tool_req 2 "TR-Sat-Decide";
        if Options.profiling() then begin
          Profiling.reset_dlevel env.dlevel;
          Profiling.reset_ilevel env.ilevel;
        end;
        let not_a = {a with E.ff = E.neg f} in
        if sat_learning () then learn_clause env not_a dep';
        let env = {env with delta=l} in
        (* in the section below, we try to backjump further with latest
           generated instances if any *)
        begin
          match update_instances_cache None with
          | None    -> assert false
          | Some [] -> ()
          | Some l  ->
            (* backtrack further if Unsat is raised by the assume below *)
            ignore (assume env l);
            (*No backtrack, reset cache*)
            ignore (update_instances_cache (Some []));
        end;
        assert (cdcl_same_decisions env);
        if Options.tableaux_cdcl () then
          cdcl_learn_clause false env dep' (E.neg f);
        print_decisions_in_the_sats "make_one_decision:backtrack" env;
        assert (cdcl_same_decisions env);
        if not (Options.tableaux_cdcl ()) then
          unsat_rec (assume env [b, Ex.union d dep']) (not_a,dep') false
        else
          match CDCL.is_true !(env.cdcl) a.E.ff with
          | Some (ex, _lvl) -> (* it is a propagation in satML *)
            if verbose() then
              fprintf fmt "Youpii ! Better BJ thanks to satML@.";
            let ex = Lazy.force ex in
            assert (not (Ex.mem (Ex.Bj f) ex));
            Ex.union dep' ex
          | None ->
            unsat_rec (assume env [b, Ex.union d dep']) (not_a,dep') false
      with Not_found ->
        Debug.backjumping (E.neg f) env;
        Options.tool_req 2 "TR-Sat-Backjumping";
        dep
    with Propagate (ff, ex) ->
      assert (cdcl_same_decisions env);
      back_tracking (assume env [ff, ex])

  let max_term_depth_in_sat env =
    let aux mx f = max mx (E.depth f) in
    let max_t = ME.fold (fun f _ mx -> aux mx f) env.gamma 0 in
    ME.fold (fun _ (f,_) mx -> aux mx f) env.ground_preds max_t


  let rec backward_instantiation_rec env rnd max_rnd =
    Debug.print_nb_related env;
    if rnd > max_rnd then env
    else
      let nb1 = env.nb_related_to_goal in
      if verbose () || debug_sat () then
        fprintf fmt "[sat.backward] round %d / %d@." rnd max_rnd;
      let mconf =
        {Util.nb_triggers = nb_triggers ();
         no_ematching = no_Ematching();
         triggers_var = triggers_var ();
         use_cs = false;
         greedy = greedy ();
         backward = Util.Backward;
        }
      in
      let env, new_i1 = inst_and_assume mconf env inst_predicates env.inst in
      let env, new_i2 = inst_and_assume mconf env inst_lemmas env.inst in
      let nb2 = env.nb_related_to_goal in
      if verbose () || debug_sat () then
        fprintf fmt "[sat.backward] backward: %d goal-related hyps (+%d)@."
          nb2 (nb2-nb1);

      if (new_i1 || new_i2) && nb1 < nb2 then
        backward_instantiation_rec env (rnd+1) max_rnd
      else env


  let backward_instantiation env deepest_term =
    try
      let no_Ematching = Options.no_Ematching () in
      let no_NLA = Options.no_NLA () in
      let no_ac = Options.no_ac () in
      let greedy = Options.greedy () in
      (*let normalize_instances = Options.normalize_instances () in*)
      let max_split = Options.max_split () in

      Options.set_no_Ematching true;
      Options.set_no_NLA true;
      Options.set_no_ac  true;
      Options.set_greedy true;
      (*Options.set_normalize_instances true;*)
      Options.set_max_split Numbers.Q.zero;

      let max_rnd = 2 * deepest_term in
      let modified_env = backward_instantiation_rec env 1 max_rnd in

      Options.set_no_Ematching no_Ematching;
      Options.set_no_NLA no_NLA;
      Options.set_no_ac  no_ac;
      Options.set_greedy greedy;
      (*Options.set_normalize_instances normalize_instances;*)
      Options.set_max_split max_split;

      let l =
        ME.fold
          (fun _ (ff, ex, _dlvl, plvl) acc ->
             if ff.E.gdist >= 0 then (ff, ex, plvl) :: acc else acc
          )modified_env.gamma []
      in
      let l =
        List.fast_sort (fun (ff1, _, plvl1) (ff2, _, plvl2) ->
            let c = ff2.E.gdist - ff1.E.gdist in
            if c <> 0 then c else plvl2 - plvl1
          )l
      in
      let l = List.rev_map (fun (ff, ex, _) -> ff, ex) l in
      if verbose () || debug_sat () then
        List.iter
          (fun (ff, _ex) ->
             fprintf fmt "%2d : %a@.@." ff.E.gdist E.print ff.E.ff
          )l;
      let env = assume env l in
      Debug.print_nb_related env;
      if verbose () || debug_sat () then
        fprintf fmt "[sat.backward] done (after %2.4f seconds)\n@."
          (Options.Time.value ());
      env
    with IUnsat _ as e ->
      if verbose () || debug_sat () then
        fprintf fmt "[sat.backward] solved with backward !@.";
      raise e

  let unsat env gf =
    Debug.is_it_unsat gf;
    try
      if Options.tableaux_cdcl () then
        cdcl_assume false env [gf,Ex.empty];
      let env = assume env [gf, Ex.empty] in
      let env =
        {env with inst = (* add all the terms of the goal to matching env *)
                    Inst.add_terms env.inst
                      (E.max_ground_terms_rec_of_form gf.E.ff) gf}
      in
      (* this includes axioms and ground preds but not general predicates *)
      let max_t = max_term_depth_in_sat env in
      let env = {env with inst = Inst.register_max_term_depth env.inst max_t} in

      let env =
        if Options.no_backward () then env
        else backward_instantiation env max_t
      in

      let env = new_inst_level env in

      let env, _ = syntactic_th_inst env env.inst ~rm_clauses:true in
      let env, _ = semantic_th_inst  env env.inst ~rm_clauses:true ~loop:4 in

      let mconf =
        {Util.nb_triggers = nb_triggers ();
         no_ematching = no_Ematching();
         triggers_var = triggers_var ();
         use_cs = false;
         backward = Util.Normal;
         greedy = greedy ();
        }
      in
      let env, _ = inst_and_assume mconf env inst_predicates env.inst in

      let env, _ = syntactic_th_inst env env.inst ~rm_clauses:true in
      let env, _ = semantic_th_inst  env env.inst ~rm_clauses:true ~loop:4 in

      (* goal directed for lemmas *)
      let gd, _ =
        inst_lemmas mconf  env env.inst env.tbox (selector env) env.ilevel
      in
      if Options.tableaux_cdcl () then
        cdcl_assume false env gd;
      if Options.profiling() then Profiling.instances gd;
      let env = assume env gd in

      let env, _ = syntactic_th_inst env env.inst ~rm_clauses:true in
      let env, _ = semantic_th_inst  env env.inst ~rm_clauses:true ~loop:4 in

      let d = back_tracking env in
      assert (Ex.has_no_bj d);
      get_all_models_answer ();
      terminated_normally := true;
      d
    with
    | IUnsat (dep, classes) ->
      Debug.bottom classes;
      Debug.unsat ();
      get_all_models_answer ();
      terminated_normally := true;
      assert (Ex.has_no_bj dep);
      dep
    | Util.Timeout when switch_to_model_gen env -> do_switch_to_model_gen env

  let assume env fg dep =
    try
      if Options.tableaux_cdcl () then
        cdcl_assume false env [fg,dep];
      assume env [fg,dep]
    with
    | IUnsat (d, classes) ->
      terminated_normally := true;
      Debug.bottom classes;
      raise (Unsat d)
    | Util.Timeout when switch_to_model_gen env -> do_switch_to_model_gen env


  (* unused --
     let factorize_iff a_t f =
     if E.equal a_t f then E.vrai
     else if E.equal (E.neg a_t) f then E.faux
     else match E.form_view f with
      | E.Iff(f1, f2) ->
        if E.equal f1 a_t then f2
        else if E.equal f2 a_t then f1
        else assert false
      | E.Not_a_form | E.Unit _ | E.Clause _ | E.Xor _
      | E.Literal _ | E.Lemma _ | E.Skolem _ | E.Let _ -> assert false
  *)

  let pred_def env f name dep _loc =
    Debug.pred_def f;
    let gf = mk_gf f name true false in
    let a_t = E.mk_term (Symbols.name name) [] Ty.Tbool in
    if not (SE.mem a_t (E.max_ground_terms_rec_of_form f)) then
      {env with
       inst = Inst.add_predicate env.inst gf dep }
    else
      begin
        assert (not (ME.mem a_t env.ground_preds));
        if E.equal a_t f || E.equal (E.neg a_t) f then assume env gf dep
        else match E.form_view f with
          | E.Iff(f1, f2) ->
            let f_simpl =
              if E.equal f1 a_t then f2
              else (if E.equal f2 a_t then f1 else assert false)
            in
            let gp = ME.add a_t (f_simpl, dep) env.ground_preds in
            let gp = ME.add (E.neg a_t) (E.neg f_simpl, dep) gp in
            {env with ground_preds = gp}
          | E.Not_a_form | E.Unit _ | E.Clause _ | E.Xor _
          | E.Literal _ | E.Lemma _ | E.Skolem _ | E.Let _ -> assert false
      end

  let unsat env fg =
    if Options.timers() then
      try
        Timers.exec_timer_start Timers.M_Sat Timers.F_unsat;
        let env = unsat env fg in
        Timers.exec_timer_pause Timers.M_Sat Timers.F_unsat;
        env
      with e ->
        Timers.exec_timer_pause Timers.M_Sat Timers.F_unsat;
        raise e
    else unsat env fg

  let assume env fg =
    if Options.timers() then
      try
        Timers.exec_timer_start Timers.M_Sat Timers.F_assume;
        let env = assume env fg in
        Timers.exec_timer_pause Timers.M_Sat Timers.F_assume;
        env
      with e ->
        Timers.exec_timer_pause Timers.M_Sat Timers.F_assume;
        raise e
    else assume env fg

  let reset_refs () =
    Options.reset_steps ();
    all_models_sat_env := None;
    latest_saved_env := None;
    terminated_normally := false

  let empty () =
    (* initialize some structures in SAT.empty. Otherwise, E.faux is never
       added as it is replaced with (not E.vrai) *)
    reset_refs ();
    let gf_true = mk_gf E.vrai "" true true in
    let inst = Inst.empty in
    let tbox = Th.empty () in
    let inst = Inst.add_terms inst (SE.singleton E.vrai) gf_true in
    let inst = Inst.add_terms inst (SE.singleton E.faux) gf_true in
    let tbox = Th.add_term tbox E.vrai ~add_in_cs:true in
    let tbox = Th.add_term tbox E.faux ~add_in_cs:true in
    let env = {
      gamma = ME.empty;
      nb_related_to_goal = 0;
      nb_related_to_hypo = 0;
      nb_related_to_both = 0;
      nb_unrelated = 0;
      cdcl = ref (CDCL.empty ());
      tcp_cache = ME.empty;
      delta = [] ;
      decisions = ME.empty;
      dlevel = 0;
      plevel = 0;
      ilevel = 0;
      tbox = tbox;
      unit_tbox = tbox;
      inst = inst;
      heuristics = ref (Heuristics.empty ());
      model_gen_mode = ref false;
      ground_preds = ME.empty;
      unit_facts_cache = ref ME.empty;
      add_inst = fun _ -> true;
    }
    in
    assume env gf_true Ex.empty
  (*maybe usefull when -no-theory is on*)

  let empty_with_inst add_inst =
    { (empty ()) with add_inst = add_inst }

  let assume_th_elt env th_elt dep =
    {env with tbox = Th.assume_th_elt env.tbox th_elt dep}
end
