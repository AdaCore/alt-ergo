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

open Format
open Options
open Sig
open Exception

module X = Combine.Shostak
module Ex = Explanation
module SetF = Formula.Set
module T = Term
module A = Literal
module LR = A.Make(struct type t = X.r let compare = X.str_cmp include X end)
module SetT = Term.Set
module Sy = Symbols


module CC_X = Ccx.Main

module type S = sig
  type t

  val empty : unit -> t

  (* the first int is the decision level (dlvl) and the second one is the
     propagation level (plvl). The facts (first argument) are sorted in
     decreasing order with respect to (dlvl, plvl) *)
  val assume :
    ?ordered:bool ->
    (Literal.LT.t * Explanation.t * int * int) list -> t ->
    t * Term.Set.t * int

  val query : Literal.LT.t -> t -> answer
  val class_of : t -> Term.t -> Term.t list
  val are_equal : t -> Term.t -> Term.t -> answer
  val print_model : Format.formatter -> t -> unit
  val cl_extract : t -> Term.Set.t list
  val term_repr : t -> Term.t -> Term.t
  val extract_ground_terms : t -> Term.Set.t
  val get_real_env : t -> Ccx.Main.t
  val get_case_split_env : t -> Ccx.Main.t
end

module Main_Default : S = struct

  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct

    let forall_of_assumed ll =
      let s =
        List.fold_left
          (fun acc l ->
            List.fold_left
              (fun s (a,_,_) -> Term.Set.union s (Literal.LT.terms_rec a)) acc l
          ) T.Set.empty ll
      in
      Term.Set.iter
        (fun t ->
          let {T.f;xs;ty} = Term.view t in
          if xs = [] then fprintf fmt "forall %a : %a.@." T.print t Ty.print ty
        )s

    let assumed l =
      if debug_cc () then
        begin
          fprintf fmt "[cc] Assumed facts (in this order):@.";
          forall_of_assumed l;
          List.iter
            (fun l ->
              fprintf fmt "@.(*call to assume*)@.";
              match l with
              | [] -> assert false
              | (a,dlvl,plvl)::l ->
                fprintf fmt "(@. (* %d , %d *) %a " dlvl plvl
                  Literal.LT.print a;
              List.iter
                (fun (a, dlvl, plvl) ->
                    fprintf fmt " and@. (* %d , %d *) %a " dlvl plvl
                    Literal.LT.print a
            ) (List.rev l);
                fprintf fmt "@.)@. ->@."
            ) (List.rev l);
          fprintf fmt "true@.";
        end

    let begin_case_split () =
      if debug_split () then
	fprintf fmt "============= Begin CASE-SPLIT ===============@."

    let end_case_split () =
      if debug_split () then
	fprintf fmt "============= End CASE-SPLIT ===============@."

    let split_size sz =
      if debug_split () then
	fprintf fmt ">size case-split: %s@." (Numbers.Q.to_string sz)

    let print_lr_view fmt ch = LR.print fmt (LR.make ch)

    let split_backtrack neg_c ex_c =
      if debug_split () then
        fprintf fmt "[case-split] I backtrack on %a : %a@."
          print_lr_view neg_c Ex.print ex_c

    let split_assume c ex_c =
      if debug_split () then
        fprintf fmt "[case-split] I assume %a : %a@."
          print_lr_view c Ex.print ex_c

    let split_backjump c dep =
      if debug_split () then
        fprintf fmt "[case-split] I backjump on %a : %a@."
          print_lr_view c Ex.print dep

    let query a =
      if debug_cc () then fprintf fmt "[cc] query : %a@." A.LT.print a

    let split () =
      if debug_split () then
        fprintf fmt "[case-split] I replay choices@."
  end
  (*BISECT-IGNORE-END*)

  type choice_sign =
    | CPos of Ex.exp (* The explication of this choice *)
    | CNeg (* The choice has been already negated *)


  type t = {
    assumed : (Literal.LT.t * int * int) list list;
    terms : Term.Set.t;
    gamma : CC_X.t;
    gamma_finite : CC_X.t;
    choices : (X.r Literal.view * lit_origin * choice_sign * Ex.t) list;
  (** the choice, the size, choice_sign,  the explication set,
      the explication for this choice. *)
  }

  let look_for_sat ?(bad_last=No) ch t base_env l =
    let rec aux ch bad_last dl base_env li =
      Options.exec_thread_yield ();
      match li, bad_last with
        | [], _ ->
	  begin
	    Options.tool_req 3 "TR-CCX-CS-Case-Split";
            match CC_X.case_split base_env with
	      | [] ->
		{ t with gamma_finite = base_env; choices = List.rev dl }, ch
	      | l ->
	        let l =
		  List.map
		    (fun (c, ex_c, size) ->
                      let exp = Ex.fresh_exp () in
                      Options.incr_cs_steps();
                      let ex_c_exp = Ex.add_fresh exp ex_c in
                      (* A new explanation in order to track the choice *)
                      (c, size, CPos exp, ex_c_exp)) l in
	        (*let sz =
		  List.fold_left
		    (fun acc (a,s,_,_) ->
		      Numbers.Q.mult acc s) (Numbers.Q.one) (l@dl) in
                Debug.split_size sz;
	        if Numbers.Q.compare sz (max_split ()) <= 0  ||
		  Numbers.Q.sign  (max_split ()) < 0 then*)
		  aux ch No dl base_env l
	        (*else
		  { t with gamma_finite = base_env; choices = List.rev dl }, ch
                *)
	  end
        | ((c, lit_orig, CNeg, ex_c) as a)::l, _ ->
          let facts = CC_X.empty_facts () in
          CC_X.add_fact facts (LSem c,ex_c,lit_orig);
	  let base_env, ch = CC_X.assume_literals base_env ch facts in
	  aux ch bad_last (a::dl) base_env l

        (** This optimisation is not correct with the current explanation *)
        (* | [(c, lit_orig, CPos exp, ex_c)], Yes (dep,_) -> *)
        (*     let neg_c = CC_X.Rel.choice_mk_not c in *)
        (*     let ex_c = Ex.union ex_c dep in *)
        (*     Debug.split_backtrack neg_c ex_c; *)
        (*     aux ch No dl base_env [neg_c, Numbers.Q.Int 1, CNeg, ex_c] *)

        | ((c, lit_orig, CPos exp, ex_c_exp) as a)::l, _ ->
	  try
            Debug.split_assume c ex_c_exp;
            let facts = CC_X.empty_facts () in
            CC_X.add_fact facts (LSem c, ex_c_exp, lit_orig);
	    let base_env, ch =  CC_X.assume_literals base_env ch facts in
	    Options.tool_req 3 "TR-CCX-CS-Normal-Run";
	    aux ch bad_last (a::dl) base_env l
	  with Exception.Inconsistent (dep, classes) ->
            match Ex.remove_fresh exp dep with
              | None ->
                (* The choice doesn't participate to the inconsistency *)
                Debug.split_backjump c dep;
		Options.tool_req 3 "TR-CCX-CS-Case-Split-Conflict";
                raise (Exception.Inconsistent (dep, classes))
              | Some dep ->
		Options.tool_req 3 "TR-CCX-CS-Case-Split-Progress";
                (* The choice participates to the inconsistency *)
                let neg_c = LR.view (LR.neg (LR.make c)) in
                let lit_orig = match lit_orig with
                  | CS(k, sz) -> NCS(k, sz)
                  | _ -> assert false
                in
	        Debug.split_backtrack neg_c dep;
		if bottom_classes () then
		  printf "bottom (case-split):%a\n@."
		    Term.print_tagged_classes classes;
		aux ch No dl base_env [neg_c, lit_orig, CNeg, dep]
    in
    aux ch bad_last (List.rev t.choices) base_env l

  let try_it f t =
    Options.exec_thread_yield ();
    Debug.begin_case_split ();
    let r =
      try
	if t.choices = [] then look_for_sat [] t t.gamma []
	else
	  try
	    let env, ch = f t.gamma_finite in
	    look_for_sat ch t env []
	  with Exception.Inconsistent (dep, classes) ->
            Debug.split ();
	    Options.tool_req 3 "TR-CCX-CS-Case-Split-Erase-Choices";
	    (* we replay the conflict in look_for_sat, so we can
	       safely ignore the explanation which is not useful *)
	    look_for_sat ~bad_last:(Yes (dep, classes))
	      [] { t with choices = []} t.gamma t.choices
      with Exception.Inconsistent (d, cl) ->
	Debug.end_case_split ();
	Options.tool_req 3 "TR-CCX-CS-Conflict";
	raise (Exception.Inconsistent (d, cl))
    in
    Debug.end_case_split (); r


  let extract_from_semvalues acc l =
    List.fold_left
      (fun acc r ->
	match X.term_extract r with
	  | Some t, _ -> SetT.add t acc | _ -> acc) acc l

  let extract_terms_from_choices =
    List.fold_left
      (fun acc (a, _, _, _) ->
        match a with
          | A.Eq(r1, r2) -> extract_from_semvalues acc [r1; r2]
          | A.Distinct (_, l) -> extract_from_semvalues acc l
          | A.Pred(p, _) -> extract_from_semvalues acc [p]
          | _ -> acc
      )

  let extract_terms_from_assumed =
    List.fold_left
      (fun acc (a, _, _) ->
	match a with
	  | LTerm r -> begin
	    match Literal.LT.view r with
	      | Literal.Eq (t1, t2) ->
		SetT.add t1 (SetT.add t2 acc)
	      | Literal.Distinct (_, l) | Literal.Builtin (_, _, l) ->
		List.fold_right SetT.add l acc
	      | Literal.Pred (t1, _) ->
		SetT.add t1 acc

	  end
	  | _ -> acc)

  let rec is_ordered_list l = match l with
    | [] | [[_]] -> true
    | []::r -> is_ordered_list r
    | [e]::r1::r2 -> is_ordered_list ((e::r1)::r2)
    | (e1::e2::l)::r ->
      let _, d1, p1 = e1 in
      let _, d2, p2 = e2 in
      (d1 > d2 || d1 = d2 && p1 > p2) && is_ordered_list ((e2::l)::r)

  (* facts are sorted in decreasing order with respect to (dlvl, plvl) *)
  let assume ordered in_facts t =
    let facts = CC_X.empty_facts () in
    let assumed, cpt =
      List.fold_left
        (fun (assumed, cpt) ((a, ex, dlvl, plvl)) ->
          CC_X.add_fact facts (LTerm a, ex, Sig.Other);
          (a, dlvl, plvl) :: assumed, cpt+1
        )([], 0) in_facts
    in
    let t = {t with assumed = assumed :: t.assumed} in
    if Options.profiling() then Profiling.assume cpt;
    Debug.assumed t.assumed;
    assert (not ordered || is_ordered_list t.assumed);
    let copy_facts =
      let open CC_X in
      { equas = Queue.copy facts.equas;
        diseqs = Queue.copy facts.diseqs;
        ineqs = Queue.copy facts.ineqs;
        touched = facts.touched }
    in
    let gamma, ch = CC_X.assume_literals t.gamma [] facts in
    let t = { t with gamma = gamma } in
    let t, ch = try_it (fun env -> CC_X.assume_literals env ch copy_facts) t  in
    let choices = extract_terms_from_choices SetT.empty t.choices in
    let choices_terms = extract_terms_from_assumed choices ch in
    let new_terms = CC_X.new_terms t.gamma in
    let terms = T.Set.union choices_terms new_terms in
    {t with terms = Term.Set.union t.terms terms}, terms, cpt

  let class_of t term = CC_X.class_of t.gamma term

  let add_and_process a t =
    Options.exec_thread_yield ();
    let aux a ex env =
      let gamma, facts = CC_X.add env (CC_X.empty_facts()) a ex in
      CC_X.assume_literals gamma [] facts
    in
    let gamma, _ = aux a Ex.empty t.gamma in
    let t = { t with gamma = gamma } in
    let t, _ =  try_it (aux a Ex.empty) t in
    t

  let query a t =
    if Options.profiling() then Profiling.query();
    Options.exec_thread_yield ();
    Debug.query a;
    try
      match A.LT.view a with
	| A.Eq (t1, t2)  ->
	  let t = add_and_process a t in
          CC_X.are_equal t.gamma t1 t2

	| A.Distinct (false, [t1; t2]) ->
	  let na = A.LT.neg a in
	  let t = add_and_process na t in (* na ? *)
	  CC_X.are_distinct t.gamma t1 t2

	| A.Distinct _ ->
	  assert false (* devrait etre capture par une analyse statique *)

        | A.Pred (t1,b) ->
	  let t = add_and_process a t in
          if b
          then CC_X.are_distinct t.gamma t1 (Term.top())
          else CC_X.are_equal t.gamma t1 (Term.top())

	| _ ->
	  let na = A.LT.neg a in
	  let t = add_and_process na t in
          CC_X.query t.gamma na
    with Exception.Inconsistent (d, classes) ->
      Yes (d, classes)

  let are_equal t t1 t2 =
    let gamma, facts = CC_X.add_term t.gamma (CC_X.empty_facts()) t1 Ex.empty in
    let gamma, facts = CC_X.add_term gamma facts t2 Ex.empty in
    try
      let gamma, _ = CC_X.assume_literals gamma [] facts in
      CC_X.are_equal gamma t1 t2
    with Inconsistent (ex,cl) -> Yes(ex, cl)

  let empty () =
    let env = CC_X.empty () in
    let env, _ = CC_X.add_term env (CC_X.empty_facts()) T.vrai Ex.empty in
    let env, _ = CC_X.add_term env (CC_X.empty_facts()) T.faux Ex.empty in
    let t =
      { gamma = env;
        gamma_finite = env;
        choices = [];
        assumed = [];
        terms = Term.Set.empty }
    in
    let a = A.LT.mk_distinct false [T.vrai; T.faux] in
    let t, _, _ = assume true [a, Ex.empty, 0, -1] t in
    t

  let print_model fmt t = CC_X.print_model fmt t.gamma_finite

  let cl_extract env = CC_X.cl_extract env.gamma

  let term_repr env t = CC_X.term_repr env.gamma t

  let assume ?(ordered=true) facts t =
    if Options.timers() then
      try
	Options.exec_timer_start Timers.M_CC Timers.F_assume;
	let res = assume ordered facts t in
	Options.exec_timer_pause Timers.M_CC Timers.F_assume;
	res
      with e ->
	Options.exec_timer_pause Timers.M_CC Timers.F_assume;
	raise e
    else assume ordered facts t

  let query a t =
    if Options.timers() then
      try
	Options.exec_timer_start Timers.M_CC Timers.F_query;
	let res = query a t in
	Options.exec_timer_pause Timers.M_CC Timers.F_query;
	res
      with e ->
	Options.exec_timer_pause Timers.M_CC Timers.F_query;
	raise e
    else query a t

  let class_of t term =
    if Options.timers() then
      try
	Options.exec_timer_start Timers.M_CC Timers.F_class_of;
	let res = class_of t term in
	Options.exec_timer_pause Timers.M_CC Timers.F_class_of;
	res
      with e ->
	Options.exec_timer_pause Timers.M_CC Timers.F_class_of;
	raise e
    else class_of t term

  let extract_ground_terms env = env.terms

  let get_real_env t = t.gamma
  let get_case_split_env t = t.gamma_finite


  let are_equal env t1 t2 =
    if Options.timers() then
      try
	Options.exec_timer_start Timers.M_CC Timers.F_are_equal;
	let res = are_equal env t1 t2 in
	Options.exec_timer_pause Timers.M_CC Timers.F_are_equal;
	res
      with e ->
	Options.exec_timer_pause Timers.M_CC Timers.F_are_equal;
	raise e
    else are_equal env t1 t2

end

module Main_Empty : S = struct

  type t = int

  let empty () = -1

  let assume ?(ordered=true) _ _ = 0, T.Set.empty, 0
  let query a t = No
  let class_of env t = [t]
  let are_equal env t1 t2 = if T.equal t1 t2 then Yes(Ex.empty, []) else No
  let print_model _ _ = ()
  let cl_extract _ = []
  let term_repr _ t = t
  let extract_ground_terms _ = Term.Set.empty

  let empty_ccx = CC_X.empty ()
  let get_real_env _ = empty_ccx
  let get_case_split_env _ = empty_ccx

end

module Main =
  (val
      (
        if Options.no_theory() then (module Main_Empty : S)
        else (module Main_Default : S)
      ) : S
  )
