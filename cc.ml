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

open Format
open Options
open Sig
open Exception


module type S = sig
  type t

  val empty : unit -> t
  val assume : Literal.LT.t -> Explanation.t -> t -> t * Term.Set.t * int
  val query : Literal.LT.t -> t -> answer
  val class_of : t -> Term.t -> Term.t list
end

module Make (X : Sig.X) = struct    

  module Ex = Explanation
  module SetA = Use.SA
  module Use = Use.Make(X)
  module Uf = Uf.Make(X)
  module SetF = Formula.Set
  module T = Term
  module A = Literal
  module LR = A.Make(struct type t = X.r include X end)
  module SetT = Term.Set
  module S = Symbols

  module SetX = Set.Make(struct type t = X.r let compare = X.compare end)
    
  type env = { 
    use : Use.t;  
    uf : Uf.t ;
    relation : X.Rel.t
  }

  type choice_sign =
    | CPos of Ex.exp (* The explication of this choice *)
    | CNeg (* The choice has been already negated *)

  type t = { 
    gamma : env;
    gamma_finite : env ;
    choices : (X.r A.view * Num.num * choice_sign * Ex.t) list; 
    (** the choice, the size, choice_sign,  the explication set,
        the explication for this choice. *)
  }

  module Print = struct
    
    let begin_case_split () = 
      if debug_split then
	fprintf fmt "============= Begin CASE-SPLIT ===============@."

    let end_case_split () = 
      if debug_split then
	fprintf fmt "============= End CASE-SPLIT ===============@."

    let cc r1 r2 =
      if debug_cc then 
	fprintf fmt "@{<C.Bold>[cc]@} congruence closure : %a = %a@." 
	  X.print r1 X.print r2

    let make_cst t ctx =
      if debug_cc then 
	if ctx = [] then ()
	else begin
          fprintf fmt "[cc] contraints of make(%a)@." Term.print t;
          let c = ref 0 in
          List.iter 
            (fun a ->
               incr c;
               fprintf fmt " %d) %a@." !c A.LT.print a) ctx
	end

    let add_to_use t = 
      if debug_cc then 
	fprintf fmt "@{<C.Bold>[cc]@} add_to_use: %a@." T.print t
	
    let lrepr fmt = List.iter (fprintf fmt "%a " X.print)

    let leaves t lvs = 
      fprintf fmt "@{<C.Bold>[cc]@} leaves of %a@.@." T.print t; lrepr fmt lvs
	
    let contra_congruence a ex = 
      if debug_cc then 
	fprintf fmt "[cc] find that %a %a by contra-congruence@." 
	  A.LT.print a Ex.print ex

    let split_size sz = 
      if debug_split then
	fprintf fmt ">size case-split: %s@." (Num.string_of_num sz)

    let split_backtrack neg_c ex_c = 
      if debug_split then
        fprintf fmt "[case-split] I backtrack on %a : %a@."
          LR.print neg_c Ex.print ex_c

    let split_assume c ex_c =
      if debug_split then
        fprintf fmt "[case-split] I assume %a : %a@."
          LR.print c Ex.print ex_c

    let split_backjump c dep =
      if debug_split then
        fprintf fmt "[case-split] I backjump on %a : %a@."
          LR.print c Ex.print dep

    let assume_literal sa =
      if debug_cc then
	fprintf fmt "[cc] assume literal : %a@." LR.print (LR.make sa)

    let congruent a ex =
      if debug_cc then
	fprintf fmt "[cc] new fact by conrgruence : %a ex[%a]@." 
          A.LT.print a Ex.print ex

    let query a =
      if debug_cc then fprintf fmt "[cc] query : %a@." A.LT.print a

  end
    
  let concat_leaves uf l = 
    let one, _ = X.make (Term.make (S.name "@bottom") [] Ty.Tint) in 
    let rec concat_rec acc t = 
      match  X.leaves (fst (Uf.find uf t)) , acc with
	  [] , _ -> one::acc
	| res, [] -> res
	| res , _ -> List.rev_append res acc
    in
    match List.fold_left concat_rec [] l with
	[] -> [one]
      | res -> res

  let are_equal env ex t1 t2 = 
    if T.equal t1 t2 then ex
    else match Uf.are_equal env.uf t1 t2 with
      | Yes dep -> Ex.union ex dep
      | No -> raise Exit

  let equal_only_by_congruence env ex t1 t2 acc = 
    if T.equal t1 t2 then acc
    else
      let {T.f=f1; xs=xs1; ty=ty1} = T.view t1 in
      if X.fully_interpreted f1 then acc
      else 
	let {T.f=f2; xs=xs2; ty=ty2} = T.view t2 in
        if Symbols.equal f1 f2 && Ty.equal ty1 ty2 then
	  try
            let ex = List.fold_left2 (are_equal env) ex xs1 xs2 in
            let a = A.LT.make (A.Eq(t1, t2)) in
            Print.congruent a ex;
            (LTerm a, ex) :: acc
          with Exit -> acc
        else acc

  let congruents env t1 s acc ex = 
    SetT.fold (equal_only_by_congruence env ex t1) s acc

  let rec add_term ex (env, l) t =
    if rules = 3 then fprintf fmt "[rule] TR-CCX-AddTerm@.";
    Print.add_to_use t;
    (* nothing to do if the term already exists *)
    if Uf.mem env.uf t then env, l
    else
      (* we add t's arguments in env *)
      let {T.f = f; xs = xs} = T.view t in
      let env, l = List.fold_left (add_term ex) (env, l) xs in
      (* we update uf and use *)
      let nuf, ctx  = Uf.add env.uf t in 
      Print.make_cst t ctx;
      let rt,_   = Uf.find nuf t in (* XXX : ctx only in terms *)
      let lvs = concat_leaves nuf xs in
      let nuse = Use.up_add env.use t rt lvs in
      
      (* If finitetest is used we add the term to the relation *)
      let rel = X.Rel.add env.relation rt in
      Use.print nuse;

      (* we compute terms to consider for congruence *)
      (* we do this only for non-atomic terms with uninterpreted head-symbol *)
      let st_uset = Use.congr_add nuse lvs in
      
      (* we check the congruence of each term *)
      let env = {uf = nuf; use = nuse; relation = rel} in 
      let ct = congruents env t st_uset l ex in
      env, (List.map (fun lt -> LTerm lt, ex) ctx) @ ct
	
  let add a ex env =
    match A.LT.view a with
      | A.Eq (t1, t2) -> 
	  let env, l1 = add_term ex (env, []) t1 in
	  let env, l2 = add_term ex (env, l1) t2 in
	  env, l2
      | A.Distinct (_, lt) 
      | A.Builtin (_, _, lt) ->
	  let env, l = List.fold_left (add_term ex) (env,[]) lt in
	  let lvs = concat_leaves env.uf lt in (* A verifier *)
	  let env =
	    List.fold_left
	      (fun env rx ->
		 let st, sa = Use.find rx env.use in
		 { env with 
		    use = Use.add rx (st,SetA.add (a, ex) sa) env.use }
	      ) env lvs
	  in
	  env, l

  let fold_find_with_explanation find ex l = 
    List.fold_left 
      (fun (lr, ex) t -> let r, ex_r = find t in r::lr, Ex.union ex_r ex)
      ([], ex) l

  let view find va ex_a = 
    match va with
      | A.Eq (t1, t2) ->
          let r1, ex1 = find t1 in
	  let r2, ex2 = find t2 in
	  let ex = Ex.union (Ex.union ex1 ex2) ex_a in
	  A.Eq(r1, r2), ex
      | A.Distinct (b, lt) -> 
	  let lr, ex = fold_find_with_explanation find ex_a lt in 
	  A.Distinct (b, lr), ex
      | A.Builtin(b, s, l) -> 
	  let lr, ex  = fold_find_with_explanation find ex_a l in
	  A.Builtin(b, s, List.rev lr), ex

  let term_canonical_view env a ex_a =  
    view (Uf.find env.uf) (A.LT.view a) ex_a

  let canonical_view env a ex_a = view (Uf.find_r env.uf) a ex_a

  let new_facts_by_contra_congruence env r bol ex = 
    match X.term_extract r with
      | None -> []
      | Some t1 -> 
	  match T.view t1 with
	    | {T.f=f1 ; xs=[x]} -> 
		List.fold_left 
		  (fun acc t2 ->
		     match T.view t2 with
		       | {T.f=f2 ; xs=[y]} when S.equal f1 f2 ->
			   let a = A.LT.make (A.Distinct (false, [x; y])) in
			   let dist = LTerm a in
			   begin match Uf.are_distinct env.uf t1 t2 with
			     | Yes ex' -> 
				 let ex_r = Ex.union ex ex' in
				 Print.contra_congruence a ex_r;
				 (dist, ex_r) :: acc
			     | No -> assert false
			 end
		       | _ -> acc
		  ) [] (Uf.class_of env.uf bol)
	    | _ -> []

  let contra_congruence  = 
    let vrai,_ = X.make T.vrai in
    let faux, _ = X.make T.faux in
    fun env r ex -> 
      if X.equal (fst (Uf.find_r env.uf r)) vrai then
	  new_facts_by_contra_congruence env r T.faux ex
      else if X.equal (fst (Uf.find_r env.uf r)) faux then
	  new_facts_by_contra_congruence env r T.vrai ex
      else []

  let clean_use = 
    List.fold_left 
      (fun env (a, ex) -> 
	 match a with 
	   | LSem _ -> assert false
	   | LTerm t -> 
	       begin
		 match A.LT.view t with
		   | A.Distinct (_, lt) 
		   | A.Builtin (_, _, lt) ->
		       let lvs = concat_leaves env.uf lt in
		       List.fold_left
			 (fun env rx ->
			    let st, sa = Use.find rx env.use in
			    let sa = SetA.remove (t, ex) sa in
			    { env with use = Use.add rx (st,sa) env.use }
			 ) env lvs
		   | _ -> assert false
	       end) 

  let rec congruence_closure env r1 r2 ex = 
    Print.cc r1 r2;
    let uf, res = Uf.union env.uf r1 r2 ex in
    List.fold_left 
      (fun (env, l) (p, touched, v) ->
	 (* we look for use(p) *)
      	 let p_t, p_a = Use.find p env.use in
	 
	 (* we compute terms and atoms to consider for congruence *)
	 let repr_touched = List.map (fun (_,a,_) -> a) touched in
	 let st_others, sa_others = Use.congr_close_up env.use p repr_touched in
	 
	 (* we update use *)
	 let nuse = Use.up_close_up env.use p v in
	 Use.print nuse;
	 
	 (* we check the congruence of the terms. *)
	 let env =  {env with use=nuse} in
	 let new_eqs = 
	   SetT.fold (fun t l -> congruents env t st_others l ex) p_t l in
       	 let touched_atoms = 
	   List.map (fun (x,y,e)-> (LSem(A.Eq(x, y)), e)) touched 
	 in
	 let touched_atoms = SetA.fold (fun (a, ex) acc ->
	   (LTerm a, ex)::acc) p_a touched_atoms in
	 let touched_atoms = SetA.fold (fun (a, ex) acc ->
	   (LTerm a, ex)::acc) sa_others touched_atoms in
	 env, new_eqs @ touched_atoms 
	   
      ) ({env with uf=uf}, [])  res

  let replay_atom env sa = 
    let are_eq = Uf.are_equal env.uf in
    let are_neq = Uf.are_distinct env.uf in
    let class_of = Uf.class_of env.uf in
    let relation, result = 
      X.Rel.assume env.relation sa are_eq are_neq class_of in
    let env = { env with relation = relation } in
    let env = clean_use env result.remove in
    env, result.assume


  let semantic_view env la = 
    List.fold_left 
      (fun (env, acc, lsa) (a, ex) ->
	 match a with 
	   | LTerm ta -> 
	       let env, l = add ta ex env in
	       let sa, ex = term_canonical_view env ta ex in
	       env, l@acc, (sa, Some ta, ex)::lsa

           (* XXX si on fait canonical_view pour
	      A.Distinct, la theorie des tableaux
              part dans les choux *)
	   | LSem (A.Builtin _  (*| A.Distinct _*) as sa) ->
	       let sa, ex = canonical_view env sa ex in 
	       env, acc, (sa, None, ex)::lsa
	   | LSem sa ->
	       env, acc, (sa, None, ex)::lsa)
      (env, [], []) la
    

  let rec assume_literal lt env la =
    if la = [] then env, lt
    else 
      let env, newc, lsa = semantic_view env la in
      let env, lt = 
	List.fold_left
	  (fun (env, lt) (sa, _, ex) ->
	    Print.assume_literal sa;
	    match sa with
	      | A.Eq(r1, r2) ->
		if rules = 3 then fprintf fmt "[rule] TR-CCX-Congruence@.";
		let env, l = congruence_closure env r1 r2 ex in
		let env, lt = assume_literal lt env l in
		if Options.nocontracongru then env, lt
		else 
		  let env, lt = 
		    assume_literal lt env (contra_congruence env r1 ex) 
		  in
		  assume_literal lt env (contra_congruence env r2 ex)
	      | A.Distinct (false, lr) ->
		if rules = 3 then fprintf fmt "[rule] TR-CCX-Distinct@.";
		if Uf.already_distinct env.uf lr then env, lt
		else 
		  {env with uf = Uf.distinct env.uf lr ex}, lt
	      | A.Distinct (true, _) -> assert false
	      | A.Builtin _ ->
		if rules = 3 then fprintf fmt "[rule] TR-CCX-Builtin@.";
		env, lt)
	  (env, lt) lsa
      in
      let env, lt = assume_literal lt env newc in
      let env, l = replay_atom env lsa in
      assume_literal (lt@l) env l


  let look_for_sat ?(bad_last=No) lt t base_env l =
    let rec aux lt bad_last dl base_env li = match li, bad_last with
      | [], _ -> 
	begin
	  if rules = 3 then
	    fprintf fmt "[rule] TR-CCX-CS-Case-Split@.";
          match X.Rel.case_split base_env.relation with
	    | [] -> 
		{ t with gamma_finite = base_env; choices = List.rev dl }, lt
	    | l ->
	      let l = 
		List.map
		  (fun (c, ex_c, size) ->
                     let exp = Ex.fresh_exp () in
                     let ex_c_exp = Ex.add_fresh exp ex_c in
                     (* A new explanation in order to track the choice *)
                     (c, size, CPos exp, ex_c_exp)) l in
	      let sz =
		List.fold_left
		  (fun acc (a,s,_,_) ->
		     Num.mult_num acc s) (Num.Int 1) (l@dl) in
              Print.split_size sz;
	      if Num.le_num sz max_split then aux lt No dl base_env l
	      else
		{ t with gamma_finite = base_env; choices = List.rev dl }, lt
	end
      | ((c, size, CNeg, ex_c) as a)::l, _ ->
	  let base_env, lt = assume_literal lt base_env [LSem c, ex_c] in
	  aux lt bad_last (a::dl) base_env l

      (** This optimisation is not correct with the current explanation *)
      (* | [(c, size, CPos exp, ex_c)], Yes dep -> *)
      (*     let neg_c = LR.neg (LR.make c) in *)
      (* 	  let ex_c = Ex.union ex_c dep in *)
      (*     Print.split_backtrack neg_c ex_c; *)
      (*     aux No dl base_env [LR.view neg_c, Num.Int 1, CNeg, ex_c] *)

      | ((c, size, CPos exp, ex_c_exp) as a)::l, _ ->
	  try
            Print.split_assume (LR.make c) ex_c_exp;
	    let base_env, lt = assume_literal lt base_env [LSem c, ex_c_exp] in
	    if rules = 3 then
	      fprintf fmt "[rule] TR-CCX-CS-Normal-Run@.";
	    aux lt bad_last (a::dl) base_env l
	  with Exception.Inconsistent dep ->
            match Ex.remove_fresh exp dep with
              | None ->
                (* The choice doesn't participate to the inconsistency *)
                Print.split_backjump (LR.make c) dep;
		if rules = 3 then
		  fprintf fmt "[rule] TR-CCX-CS-Case-Split-Conflict@.";
                raise (Exception.Inconsistent dep)
              | Some dep ->
		if rules = 3 then
		  fprintf fmt "[rule] TR-CCX-CS-Case-Split-Progress@.";
                (* The choice participates to the inconsistency *)
                let neg_c = LR.neg (LR.make c) in
	        Print.split_backtrack neg_c dep;
	        aux lt No dl base_env [LR.view neg_c, Num.Int 1, CNeg, dep]
    in
    aux lt bad_last (List.rev t.choices) base_env l

  let try_it f t =
    Print.begin_case_split ();
    let r =
      try 
	if t.choices = [] then look_for_sat [] t t.gamma []
	else
	  try
	    let env, lt = f t.gamma_finite in
	    look_for_sat lt t env []
	  with Exception.Inconsistent dep -> 
            if debug_split then
              fprintf fmt "[case-split] I replay choices@.";
	    if rules = 3 then
	      fprintf fmt "[rule] TR-CCX-CS-Case-Split-Erase-Choices@.";
	    (* we replay the conflict in look_for_sat, so we can
	       safely ignore the explanation which is not useful *)
	    look_for_sat ~bad_last:(Yes dep)
	      [] { t with choices = []} t.gamma t.choices
      with Exception.Inconsistent d ->
	Print.end_case_split ();
	if rules = 3 then
	  fprintf fmt "[rule] TR-CCX-CS-Conflict@.";
	raise (Exception.Inconsistent d)
    in
    Print.end_case_split (); r

  let extract_from_semvalues =
    List.fold_left
      (fun acc r -> 
	 match X.term_extract r with Some t -> SetT.add t acc | _ -> acc) 
      
  let extract_terms_from_choices = 
    List.fold_left 
      (fun acc (a, _, _, _) -> 
	 match a with
	   | A.Eq(r1, r2) -> extract_from_semvalues acc [r1; r2]
	   | A.Distinct (_, l) -> extract_from_semvalues acc l
	   | _ -> acc) 

  let extract_terms_from_assumed = 
    List.fold_left 
      (fun acc (a, _) -> 
	 match a with
	   | LTerm r -> begin
	       match Literal.LT.view r with 
		 | Literal.Eq (t1, t2) -> 
		     SetT.add t1 (SetT.add t2 acc)
		 | Literal.Distinct (_, l) | Literal.Builtin (_, _, l) -> 
		     List.fold_right SetT.add l acc
	     end
	   | _ -> acc)

  let assume a ex t = 
    let a = LTerm a in
    let gamma, lt = assume_literal [] t.gamma [a, ex] in
    let t = { t with gamma = gamma } in
    let t, lt = try_it (fun env -> assume_literal lt env [a, ex] ) t  in 
    let choices = extract_terms_from_choices SetT.empty t.choices in
    let all_terms = extract_terms_from_assumed choices lt in
    t, all_terms, 1

  let class_of t term = Uf.class_of t.gamma.uf term

  let add_and_process a t =
    let aux a ex env = 
      let gamma, l = add a ex env in assume_literal [] gamma l
    in
    let gamma, _ = aux a Ex.empty t.gamma in
    let t = { t with gamma = gamma } in
    let t, _ =  try_it (aux a Ex.empty) t in
    Use.print t.gamma.use; t    

  let query a t =
    Print.query a;
    try
        match A.LT.view a with
	| A.Eq (t1, t2)  ->
	  let t = add_and_process a t in
	  Uf.are_equal t.gamma.uf t1 t2

	| A.Distinct (false, [t1; t2]) -> 
	  let na = A.LT.neg a in
	  let t = add_and_process na t in (* na ? *)
	  Uf.are_distinct t.gamma.uf t1 t2

	| A.Distinct _ -> 
	  assert false (* devrait etre capture par une analyse statique *)

	| _ -> 
	  let na = A.LT.neg a in
	  let t = add_and_process na t in
	  let env = t.gamma in
	  let are_eq = Uf.are_equal env.uf in
	  let are_neq = Uf.are_distinct env.uf in
	  let class_of = Uf.class_of env.uf in
	  let rna, ex_rna = term_canonical_view env na Ex.empty in
          X.Rel.query env.relation (rna, Some na, ex_rna) 
	    are_eq are_neq class_of
    with Exception.Inconsistent d -> Yes d

  let empty () = 
    let env = { 
      use = Use.empty ; 
      uf = Uf.empty ; 
      relation = X.Rel.empty ();
    }
    in
    let t = { gamma = env; gamma_finite = env; choices = [] } in
    let t, _, _ = 
      assume (A.LT.make (A.Distinct (false, [T.vrai; T.faux]))) Ex.empty t
    in t

end
