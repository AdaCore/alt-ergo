(**************************************************************************)
(*                                                                        *)
(*     The Alt-ergo theorem prover                                        *)
(*     Copyright (C) 2006-2010                                            *)
(*                                                                        *)
(*     Sylvain Conchon                                                    *)
(*     Evelyne Contejean                                                  *)
(*     Stephane Lescuyer                                                  *)
(*     Mohamed Iguernelala                                                *)
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
  val assume : Literal.LT.t -> Explanation.t -> t -> t * int
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

  type t = { 
    gamma : env;
    gamma_finite : env ;
    choices : (X.r A.view * Num.num * bool * Ex.t) list; 
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

  let are_equal env t1 t2 = Uf.are_equal env.uf t1 t2 <> No 

  let equal_only_by_congruence env t1 t2 = 
    if are_equal env t1 t2 then false
    else
      let {T.f=f1; xs=xs1; ty=ty1} = T.view t1 in
      if X.fully_interpreted f1 then false
      else 
	let {T.f=f2; xs=xs2; ty=ty2} = T.view t2 in
	Symbols.equal f1 f2 && Ty.equal ty1 ty2 && 
	  List.for_all2 (are_equal env) xs1 xs2

  let congruents env t1 s acc ex = 
    SetT.fold 
      (fun t2 acc -> 
	 if not (equal_only_by_congruence env t1 t2) then acc
	 else (LTerm (A.LT.make (A.Eq(t1, t2))), ex) :: acc) 
      s acc

  let rec add_term ex (env, l) t = 
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

  let fold_find_with_explanation env ex l = 
    List.fold_left 
      (fun (lr, ex) t -> 
	 let r, ex_r = Uf.find env.uf t in 
	 r::lr, Ex.union ex_r ex)
      ([], ex) l

  let semantic_view env a ex_a = 
    match A.LT.view a with
      | A.Distinct (b, lt) -> 
	  let lr, ex = fold_find_with_explanation env ex_a lt in 
	  A.Distinct (b, lr), ex
      | A.Builtin(b, s, l) -> 
	  let lr, ex  = fold_find_with_explanation env ex_a l in
	  A.Builtin(b, s, List.rev lr), ex
      | _ -> assert false

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
       	 let touched_as_eqs = 
	   List.map (fun (x,y,e)-> (LSem(A.Eq(x, y)), e)) touched 
	 in
	 env, new_eqs @ touched_as_eqs
	   
      ) ({env with uf=uf}, [])  res

  let replay_atom env sa = 
    let are_eq = Uf.are_equal env.uf in
    let are_neq = Uf.are_distinct env.uf in
    let class_of = Uf.class_of env.uf in
    let relation, result  = 
      X.Rel.assume env.relation sa are_eq are_neq class_of in
    let env = clean_use { env with relation = relation} result.remove in
    env, result.assume

  let rec assume_literal env (a, ex) =
    let env, (sa, ex), tao = 
      match a with 
	| LTerm ta -> 
	    let env, l = add ta ex env in
	    let env = List.fold_left assume_literal env l in
	    env, semantic_view env ta ex, Some ta
	| LSem sa -> env, (sa, ex), None
    in 
    match sa with
      | A.Eq(r1, r2) ->
	  let env, l = congruence_closure env r1 r2 ex in
	  let env = List.fold_left assume_literal env l in
	  if Options.nocontracongru then env
	  else 
	    let env = 
	      List.fold_left assume_literal env (contra_congruence env r1 ex) 
	    in
	    List.fold_left assume_literal env (contra_congruence env r2 ex)
      | A.Distinct (false, lr) ->
	  if Uf.already_distinct env.uf lr then env
	  else 
	    let env = {env with uf = Uf.distinct env.uf lr ex} in
	    let env , l = replay_atom env [sa, tao, ex] in
	    List.fold_left assume_literal env l
      | A.Distinct (true, _) -> assert false
      | A.Builtin _ -> 
	  let env, l = replay_atom env [sa, tao, ex] in
	  List.fold_left assume_literal env l

  let look_for_sat ?(bad_last=false) t base_env l =
    let rec aux bad_last dl base_env = function
      | [] -> 
	begin
          match X.Rel.case_split base_env.relation with
	    | [] -> 
		{ t with gamma_finite = base_env; choices = List.rev dl }
	    | l ->
		let l = List.map 
		  (fun (c,ex_c, size) -> (c, size, false, ex_c)) l in
		let sz =
		  List.fold_left
		    (fun acc (a,s,_,_) -> 
		       Num.mult_num acc s) (Num.Int 1) (l@dl) in
		Print.split_size sz;
		if Num.le_num sz max_split then aux false dl base_env l
		else
		  { t with gamma_finite = base_env; choices = List.rev dl }
	end
      | ((c, size, true, ex_c) as a)::l ->
	  let base_env = assume_literal base_env (LSem c, ex_c) in
	  aux bad_last (a::dl) base_env l

      | [(c, size, false, ex_c)] when bad_last ->
          let neg_c = LR.neg (LR.make c) in
	  Print.split_backtrack neg_c ex_c;
	  aux false dl base_env [LR.view neg_c, Num.Int 1, true, ex_c] 

      | ((c, size, false, ex_c) as a)::l ->
	  try
	    let base_env = assume_literal base_env (LSem c, ex_c) in
	    aux bad_last (a::dl) base_env l
	  with Exception.Inconsistent dep ->
            let neg_c = LR.neg (LR.make c) in
	    Print.split_backtrack neg_c dep;
	    aux false dl base_env [LR.view neg_c, Num.Int 1, true, dep] 
    in
    aux bad_last (List.rev t.choices) base_env l

  let try_it f t =
    Print.begin_case_split ();
    let r =
      try 
	if t.choices = [] then look_for_sat t t.gamma []
	else
	  try
	    let env = f t.gamma_finite in
	    look_for_sat t env []
	  with Exception.Inconsistent _ -> 
	    (* we replay the conflict in look_for_sat, so we can
	       safely ignore the explanation which is not useful *)
	    look_for_sat ~bad_last:true 
	      { t with choices = []} t.gamma t.choices
      with Exception.Inconsistent d ->
	Print.end_case_split (); 
	raise (Exception.Inconsistent d)
    in
    Print.end_case_split (); r
      
  let assume a ex t = 
    let a = LTerm a in
    let t = { t with gamma = assume_literal t.gamma (a, ex) } in
    let t = try_it (fun env -> assume_literal env (a, ex) ) t  in 
    t, 1

  let class_of t term = Uf.class_of t.gamma.uf term

  let add_and_process a ex env = 
    let gamma, l = add a ex env in
    List.fold_left assume_literal gamma l 

  let query a t = 
    try
      let t = { t with gamma = add_and_process a Ex.empty t.gamma } in
      let t =  try_it (add_and_process a Ex.empty) t in
      let env = t.gamma in
      Use.print t.gamma.use;    
      match A.LT.view a with
	| A.Eq (t1, t2)  -> 
	    Uf.are_equal env.uf t1 t2

	| A.Distinct (false, [t1; t2]) -> 
	    Uf.are_distinct env.uf t1 t2

	| A.Distinct _ -> 
	    assert false (* devrait etre capture par une analyse statique *)

	| _ -> 
	    assert false
  (* let na = A.LT.neg a in
	      let rna, ex_rna = semantic_view env na Ex.empty in
              X.Rel.query (rna, Some na) env.relation ex_rna*)
    with Exception.Inconsistent d -> Yes d

  let empty () = 
    let env = { 
      use = Use.empty ; 
      uf = Uf.empty ; 
      relation = X.Rel.empty ();
    }
    in
    let t = { gamma = env; gamma_finite = env; choices = [] } in
    fst 
      (assume 
	 (A.LT.make (A.Distinct (false, [T.vrai; T.faux])))
	 Ex.empty t)

end
