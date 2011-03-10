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

open Why_ptree

let eq_var x t = 
  match t.tt_desc with
    | TTvar y -> Symbols.equal x y
    | _ -> false

let rec find_eq x eqs = function
  | TFatom (_, (TAeq (_, [t1;t2]))) -> 
      if eq_var x t1 then (x,t2)::eqs 
      else if eq_var x t2 then (x,t1)::eqs
      else eqs
  | TFop(_, OPand,l) -> List.fold_left (find_eq x) eqs l
  | _ -> eqs (* XXX: TODO *)

let find_equalities lv f = 
  List.fold_left 
    (fun eqs (x,_) -> 
       let l = find_eq x [] f in 
       if l = [] then raise Not_found; l::eqs ) [] lv

let rec apply_subst_term env t = 
  let tt = match t.tt_desc with
    | TTvar x as tt -> 
	(try (List.assoc x env).tt_desc with Not_found -> tt)
    | TTapp(s,l) -> TTapp(s,List.map (apply_subst_term env) l)
    | TTinfix(t1,s,t2) -> 
	TTinfix(apply_subst_term env t1,s,apply_subst_term env t2)
    | tt -> tt
  in
  { t with tt_desc = tt }

let rec apply_subst_formula env f = 
  match f with
    | TFatom (ida, e) -> 
	let a = match e with
	  | TAeq (ide, l) -> TAeq (ide, List.map (apply_subst_term env) l) 
	  | TAneq (ide, l) -> TAneq (ide, List.map (apply_subst_term env) l)
	  | TAdistinct (ide, l) -> TAdistinct (ide, List.map (apply_subst_term env) l)
	  | TAle (ide, l) -> TAle (ide, List.map (apply_subst_term env) l)
	  | TAlt (ide, l) -> TAlt (ide, List.map (apply_subst_term env) l)
	  | TAbuilt(ide,s,l) -> TAbuilt(ide,s,List.map (apply_subst_term env) l)
	  | TApred (ide, t) -> TApred (ide, apply_subst_term env t)
	  | TAfalse | TAtrue -> assert false
	in TFatom (ida, a)
    | TFop(ido, op,lf) ->
	TFop(ido, op, List.map (apply_subst_formula env) lf)
    | TFforall _ | TFexists _ -> f (* XXX: TODO *)
    | _ -> f
	
let make_instance f = 
  let lt = find_equalities f.qf_bvars f.qf_form in
  apply_subst_formula (List.map List.hd lt) f.qf_form

let make f = 
  if Options.no_rm_eq_existential 
  then TFexists (0, f)
  else
    try (*TFop(OPor,[TFexists f;*)make_instance f(*])*) 
    with Not_found -> TFexists (0, f)

