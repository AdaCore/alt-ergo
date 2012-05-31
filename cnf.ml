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

open Options
open Format
open Why_ptree

module T = Term
module F = Formula
module A = Literal

let ale = Hstring.make "<="
let alt = Hstring.make "<" 

let queue = Queue.create ()

let clear () = Queue.clear queue

let varset_of_list = 
  List.fold_left 
    (fun acc (s,ty) -> 
       Term.Set.add (Term.make s [] (Ty.shorten ty)) acc) Term.Set.empty

let rec make_term {c = { tt_ty = ty; tt_desc = tt }} = 
  let ty = Ty.shorten ty in
  match tt with
    | TTconst Ttrue -> 
	T.vrai
    | TTconst Tfalse -> 
	T.faux
    | TTconst Tvoid -> 
	T.void
    | TTconst (Tint i) -> 
	T.int i
    | TTconst (Treal n) -> 
	T.real (Num.string_of_num n)
    | TTconst (Tbitv bt) -> 
	T.bitv bt ty
    | TTvar s ->  
	T.make s [] ty 
    | TTapp (s, l) -> 
	T.make s (List.map make_term l) ty
    | TTinfix (t1, s, t2) ->  
	T.make s [make_term t1;make_term t2] ty
    | TTprefix ((Symbols.Op Symbols.Minus) as s, n) ->
	let t1 = if ty = Ty.Tint then T.int "0" else T.real "0"  in
	T.make s [t1; make_term n] ty
    | TTprefix _ -> 
	assert false
    | TTget (t1, t2) ->
	T.make (Symbols.Op Symbols.Get) [make_term t1; make_term t2] ty
    | TTset (t1, t2, t3) ->
	let t1 = make_term t1 in
	let t2 = make_term t2 in
	let t3 = make_term t3 in
	T.make (Symbols.Op Symbols.Set) [t1; t2; t3] ty   
    | TTextract (t1, t2, t3) ->
	let t1 = make_term t1 in
	let t2 = make_term t2 in
	let t3 = make_term t3 in
	T.make (Symbols.Op Symbols.Extract) [t1; t2; t3] ty
    | TTconcat (t1, t2) ->
	T.make (Symbols.Op Symbols.Concat) [make_term t1; make_term t2] ty
    | TTdot (t, s) -> 
	T.make (Symbols.Op (Symbols.Access s)) [make_term t] ty
    | TTrecord lbs -> 
	let lbs = List.map (fun (_, t) -> make_term t) lbs in
	T.make (Symbols.Op Symbols.Record) lbs ty
    | TTlet (s, t1, t2) ->
	let t1 = make_term t1 in
	let subst = Symbols.Map.add s t1 Symbols.Map.empty, Ty.esubst in
	let t2 = make_term t2 in
	T.apply_subst subst t2
    | TTnamed(lbl, t) ->
	let t = make_term t in
	T.add_label lbl t;
	t

let make_trigger = function
  | [{c={ tt_desc = TTapp(s, t1::t2::l)}}] 
      when Symbols.equal s Common.fake_eq -> 
      let trs = List.filter (fun t -> not (List.mem t l)) [t1; t2] in
      let trs = List.map make_term trs in
      let lit = A.LT.make (A.Eq (make_term t1, make_term t2)) in
      trs, Some lit

  | [{c={ tt_desc = TTapp(s, t1::t2::l) } }] 
      when Symbols.equal s Common.fake_neq ->
      let trs = List.filter (fun t -> not (List.mem t l)) [t1; t2] in
      let trs = List.map make_term trs in
      let lit = A.LT.make (A.Distinct (false, [make_term t1; make_term t2])) in
      trs, Some lit
      
  | [{c={ tt_desc = TTapp(s, t1::t2::l) } }] 
      when Symbols.equal s Common.fake_le ->
      let trs = List.filter (fun t -> not (List.mem t l)) [t1; t2] in
      let trs = List.map make_term trs in
      let lit = 
	A.LT.make (A.Builtin(true, ale , [make_term t1; make_term t2])) 
      in
      trs, Some lit

  | [{c={ tt_desc = TTapp(s, t1::t2::l) } }] 
      when Symbols.equal s Common.fake_lt -> 
      let trs = List.filter (fun t -> not (List.mem t l)) [t1; t2] in
      let trs = List.map make_term trs in

      let lit = 
	A.LT.make (A.Builtin(true, alt, [make_term t1; make_term t2])) 
      in
      trs, Some lit

  | lt -> List.map make_term lt, None

let make_form name f = 
  let rec make_form acc c id = match c with
    | TFatom a ->
	let a , lit = match a.c with
	  | TAtrue -> 
	      A.LT.vrai , A.LT.vrai::acc
	  | TAfalse -> 
	      A.LT.faux , A.LT.faux::acc
	  | TAeq [t1;t2] -> 
	      let lit = A.LT.make (A.Eq (make_term t1, make_term t2)) in
	      lit , lit::acc
	  | TApred t ->
	      let lit = A.LT.mk_pred (make_term t) in
	      lit , lit::acc
	  | TAneq lt | TAdistinct lt -> 
	      let lt = List.map make_term lt in
	      let lit = A.LT.make (A.Distinct (false, lt)) in
	      lit , lit::acc
	  | TAle [t1;t2] -> 
	      let lit = 
		A.LT.make (A.Builtin(true,ale,[make_term t1;make_term t2]))
	      in lit , lit::acc
 	  | TAlt [t1;t2] ->  
	      begin match t1.c.tt_ty with
		| Ty.Tint -> 
		    let one = 
		      {c = {tt_ty = Ty.Tint; 
			    tt_desc = TTconst(Tint "1")}; annot = t1.annot} in
		    let tt2 = 
		      T.make (Symbols.Op Symbols.Minus) 
			[make_term t2; make_term one] Ty.Tint in
		    let lit = 
		      A.LT.make (A.Builtin(true,ale,[make_term t1; tt2]))
		    in lit , lit::acc
		| _ -> 
		    let lit = 
		      A.LT.make 
			(A.Builtin(true, alt, [make_term t1; make_term t2])) 
		    in lit, lit::acc
	      end
	  | TAbuilt(n,lt) ->
	      let lit = A.LT.make (A.Builtin(true,n,List.map make_term lt)) in
	      lit , lit::acc
	  | _ -> assert false
	in F.mk_lit a id, lit

    | TFop(((OPand | OPor) as op),[f1;f2]) -> 
	let ff1 , lit1 = make_form acc f1.c f1.annot in
	let ff2 , lit2 = make_form lit1 f2.c f2.annot in
	let mkop = match op with 
	  | OPand -> F.mk_and ff1 ff2 id
	  | _ -> F.mk_or ff1 ff2 id in
	mkop , lit2
    | TFop(OPimp,[f1;f2]) -> 
	let ff1 , _ = make_form acc f1.c f1.annot in
	let ff2 , lit = make_form acc f2.c f2.annot in
	F.mk_imp ff1 ff2 id, lit
    | TFop(OPnot,[f]) -> 
	let ff , lit = make_form acc f.c f.annot in
	F.mk_not ff , lit
    | TFop(OPif t,[f2;f3]) -> 
	let tt = make_term t in
	let ff2 , lit2 = make_form acc f2.c f2.annot in
	let ff3 , lit3 = make_form lit2 f3.c f3.annot in
	F.mk_if tt ff2 ff3 id, lit3
    | TFop(OPiff,[f1;f2]) -> 
	let ff1 , lit1 = make_form acc f1.c f1.annot in
	let ff2 , lit2 = make_form lit1 f2.c f2.annot in
	F.mk_iff ff1 ff2 id, lit2
    | (TFforall qf | TFexists qf) as f -> 
	let bvars = varset_of_list qf.qf_bvars in
	let upvars = varset_of_list qf.qf_upvars in
	let trs = List.map make_trigger qf.qf_triggers in
	let ff , lit = make_form acc qf.qf_form.c qf.qf_form.annot in
	begin match f with
	  | TFforall _ -> F.mk_forall upvars bvars trs ff name id, lit
	  | TFexists _ -> F.mk_exists upvars bvars trs ff name id, lit
	  | _ -> assert false
	end
    | TFlet(up,lvar,lterm,lf) -> 
	let ff, lit = make_form acc lf.c lf.annot in
        F.mk_let (varset_of_list up) lvar (make_term lterm) ff id, lit

    | TFnamed(lbl, f) ->
	let ff, lit = make_form acc f.c f.annot in
	F.add_label lbl ff; 
	ff, lit

    | _ -> assert false
  in
  make_form [] f.c f.annot

let push_assume f name loc match_flag = 
  let ff , _ = make_form name f in
  Queue.push {st_decl=Assume(ff, match_flag) ; st_loc=loc} queue

let push_preddef f name loc match_flag = 
  let ff , _ = make_form name f in
  Queue.push {st_decl=PredDef ff ; st_loc=loc} queue
      
let push_query n f loc = 
  let ff, lits = make_form "" f in
  Queue.push {st_decl=Query(n,ff,lits) ; st_loc=loc} queue

let make_rule ({rwt_left = t1; rwt_right = t2} as r) = 
  { r with rwt_left = make_term t1; rwt_right = make_term t2 }

let make l = 
  (*  Decl.clear ();
      Logics.clear();
      Types.clear();*)
  clear();
  (* Formula.clear_htbl (); (* Why that was needed? *) *)
  List.iter
    (fun (d,b) -> match d.c with
       | TAxiom(loc, name, f) -> push_assume f name loc b
       | TRewriting(loc, name, lr) -> 
	   Queue.push 
	     {st_decl=RwtDef(List.map make_rule lr); st_loc=loc} queue
       | TGoal(loc, sort, n, f) -> push_query n f loc
       | TPredicate_def(loc, n, [], f) -> push_assume f n loc b
       | TPredicate_def(loc, n, _, f) -> push_preddef f n loc b
       | TFunction_def(loc, n, _, _, f) -> push_assume f n loc b
       | TTypeDecl _ | TLogic _  -> ()) l;
  queue

(* For customized theories. Formulas are simplified so that the first
   part of a disjuction is a literal or a quantifier *)

type tree = Map of (F.t * tree) list | Leaf

let make_form_theory name f = 
  let make_lit a =
    match a.c with
      | TAtrue -> 
	A.LT.vrai
      | TAfalse -> 
	A.LT.faux
      | TAeq [t1;t2] -> 
	let lit = A.LT.make (A.Eq (make_term t1, make_term t2)) in
	lit
      | TApred t ->
	let lit = A.LT.mk_pred (make_term t) in
	lit
      | TAneq lt | TAdistinct lt -> 
	let lt = List.map make_term lt in
	let lit = A.LT.make (A.Distinct (false, lt)) in
	lit
      | TAle [t1;t2] -> 
	let lit = 
	  A.LT.make (A.Builtin(true,ale,[make_term t1;make_term t2]))
	in lit
      | TAlt [t1;t2] ->  
	begin match t1.c.tt_ty with
	  | Ty.Tint -> 
	    let one = 
	      {c = {tt_ty = Ty.Tint; 
		    tt_desc = TTconst(Tint "1")}; annot = t1.annot} in
	    let tt2 = 
	      T.make (Symbols.Op Symbols.Minus) 
		[make_term t2; make_term one] Ty.Tint in
	    let lit = 
	      A.LT.make (A.Builtin(true,ale,[make_term t1; tt2]))
	    in lit
	  | _ -> 
	    let lit = 
	      A.LT.make 
		(A.Builtin(true, alt, [make_term t1; make_term t2])) 
	    in lit
	end
      | TAbuilt(n,lt) ->
	let lit = A.LT.make (A.Builtin(true,n,List.map make_term lt)) in
	lit
      | _ -> assert false in

  let rec mk_and t1 t2 =
    List.fold_right (fun (f, m1) t2 ->
      try let m2 = List.assoc f t2 in
          let m = match m1, m2 with
            | m, Leaf | Leaf, m -> m
            | Map m1, Map m2 -> Map (mk_and m1 m2) in
          (f, m) :: t2
      with Not_found -> (f, m1) :: t2) t1 t2 in

  let rec mk_or t1 t2 = List.fold_right (fun (f, m1) t1 ->
    let m1 = match m1 with
        | Leaf -> Map t2
        | Map m1 -> Map (mk_or m1 t2) in
    (f, m1) :: t1) t1 [] in

  let rec reconstruct id ff d =
    match d with
      | Leaf -> ff
      | Map l ->
        match List.rev l with
          | [] -> assert false
          | (f, d) :: l ->
            let f = List.fold_left (fun ff (f, d) ->
              F.mk_and (reconstruct id f d) ff id) (reconstruct id f d) l in
            F.mk_or ff f id in

  let reconstruct l id =
    match List.rev l with
      | [] -> assert false
      | (f, d) :: l ->
        List.fold_left (fun ff (f, d) ->
          F.mk_and (reconstruct id f d) ff id) (reconstruct id f d) l in

  let rec make_form pol c id = match c with
    | TFatom a -> let a = make_lit a in
	          if pol then [F.mk_lit a id, Leaf]
                  else [F.mk_not (F.mk_lit a id), Leaf]
    | TFop(((OPand | OPor) as op),[f1;f2]) -> 
	let ff1 = make_form pol f1.c f1.annot in
	let ff2 = make_form pol f2.c f2.annot in
	let mkop = match op, pol with 
	  | OPand, true | OPor, false -> mk_and ff1 ff2
	  | _ -> mk_or ff1 ff2 in
	mkop
    | TFop(OPnot,[f]) -> 
	make_form (not pol) f.c f.annot
    | TFop(OPimp,[f1;f2]) -> 
	let ff1 = make_form (not pol) f1.c f1.annot in
	let ff2 = make_form pol f2.c f2.annot in
        if pol then mk_or ff1 ff2
        else mk_and ff1 ff2
    | TFop(OPif t,[f2;f3]) -> 
	let tt = make_term t in
        let lit = F.mk_lit (Literal.LT.mk_pred tt) id in
        let nlit = [F.mk_not lit, Leaf] in
        let lit = [lit, Leaf] in
	let ff2 = make_form pol f2.c f2.annot in
	let ff3 = make_form pol f3.c f3.annot in
        let ff1 = if pol then mk_and lit ff2
          else mk_or nlit ff2 in
        let ff2 = if pol then mk_and nlit ff3
          else mk_or lit ff3 in
        if pol then mk_or ff1 ff2
        else mk_and ff1 ff2
    | TFop(OPiff,[f1;f2]) -> 
	let ff1 = make_form pol f1.c f1.annot in
	let ff2 = make_form pol f2.c f2.annot in
	let nf1 = make_form (not pol) f1.c f1.annot in
	let nf2 = make_form (not pol) f2.c f2.annot in
        if pol then mk_and (mk_or nf1 ff2) (mk_or ff1 nf2)
        else mk_and (mk_or ff1 ff2) (mk_or nf1 nf2)
    | (TFforall qf | TFexists qf) as f -> 
	let bvars = varset_of_list qf.qf_bvars in
	let upvars = varset_of_list qf.qf_upvars in
	let trs = List.map make_trigger qf.qf_triggers in
	let ff = make_form pol qf.qf_form.c qf.qf_form.annot in
        let ff = reconstruct ff id in
	begin match f, pol with
	  | TFforall _, true | TFexists _, false -> 
            [F.mk_forall upvars bvars trs ff name id, Leaf]
	  | TFexists _, true | TFforall _, false -> 
            [F.mk_exists upvars bvars trs ff name id, Leaf]
	  | _ -> assert false
	end
    | TFlet(up,lvar,lterm,lf) -> 
	let ff = make_form pol lf.c lf.annot in
        let ff = reconstruct ff id in
        [F.mk_let (varset_of_list up) lvar (make_term lterm) ff id, Leaf]

    | TFnamed(lbl, f) ->
	make_form pol f.c f.annot

    | _ -> assert false
  in
  reconstruct (make_form true f.c f.annot) f.annot

let make_theory l =
  clear();
  List.iter
    (fun (d,b) -> match d.c with
       | TAxiom(loc, name, f) -> 
         let ff = make_form_theory name f in
         Queue.push {st_decl=Assume(ff, b) ; st_loc=loc} queue
       | TRewriting(loc, name, lr) -> assert false
       | TGoal(loc, _, n, f) -> assert false
       | TPredicate_def(loc, n, [], f) -> 
         let ff = make_form_theory n f in
         Queue.push {st_decl=Assume(ff, b) ; st_loc=loc} queue
       | TPredicate_def(loc, n, _, f) ->
         let ff = make_form_theory n f in
         Queue.push {st_decl=PredDef ff ; st_loc=loc} queue
       | TFunction_def(loc, n, _, _, f) -> 
         let ff = make_form_theory n f in
         Queue.push {st_decl=Assume(ff, b) ; st_loc=loc} queue
       | TTypeDecl _ | TLogic _  -> ()) l;
  queue
