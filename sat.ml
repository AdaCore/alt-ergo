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

open Options
open Format
open Sig

module A = Literal
module CcX = Cc.Make(Combine.CX)
module F = Formula
module M = Matching.Make(CcX) 
module SF = F.Set
module MF = F.Map
module Ex = Explanation

let steps = ref 0L

type gformula = { 
  f: F.t; 
  age: int; 
  name: F.t option; 
  mf: bool;
  gf: bool
}

type t = { 
    gamma : Ex.t MF.t; 
    delta : (gformula * gformula * Ex.t) list;
    tbox : CcX.t;
    lemmas : (int * Ex.t) MF.t;
    definitions : (int * Ex.t) MF.t;
    matching : M.t
}
      
exception Sat of t
exception Unsat of Ex.t
exception I_dont_know
exception IUnsat of Ex.t

let max_max_size = 96

module Print = struct

  let assume {f=f;age=age;name=lem;mf=mf} dep = 
    if debug_sat then
      begin
	(match F.view f with
	    F.Unit _ -> ()
	      
	  | F.Clause _ -> 
	      printf "@[@{<C.Bold>[sat]@}";
	      printf "@{<C.G_Cyan>I assume a clause@} @[%a@]@]@." F.print f
		
	  | F.Lemma _ ->
	      printf "@[@{<C.Bold>[sat]@}";
	      printf "@{<C.G_Yellow>I assume a [%d-atom] lemma: @}" (F.size f);
	      printf "@[%a@]@]@." F.print f
		
	  | F.Literal a -> 
	      let s = 
		match lem with 
		    None -> "" 
		  | Some ff -> 
		      (match F.view ff with F.Lemma xx -> xx.F.name | _ -> "") 
	      in
	      printf "\n@[@{<C.Bold>[sat]@}";
	      printf "@{<C.G_Blue_B>I assume a literal@}";
	      printf "(%s) %a@]@." s Literal.LT.print a;
	      printf "================================================@.@."
		
	  | F.Skolem{F.ssubst=s;ssubst_ty=s_ty;sf=f} ->
	      printf "@[@{<C.Bold>[sat]@} I assume a skolem %a @]@." F.print f 
		
	  | F.Let {F.lvar=lvar;lterm=lterm;lsubst=lsubst;lf=lf} ->
	      printf "@[@{<C.Bold>[sat]@} I assume a let %a =@ %a in@ %a@ @]@." 
		Symbols.print lvar Term.print lterm F.print lf);
	printf " with explanations : %a@." Explanation.print dep
      end

  let unsat () = 
    if debug_sat then printf "@[@{<C.Bold>[sat]@} @{<C.G_Red_B>unsat@}@]@."

  let mround s = 
    if debug_sat then 
      printf "@[@{<C.Bold>[sat]@} matching round of size %d@]@." s

  let decide f = 
    if debug_sat then 
      printf "@[@{<C.Bold>[sat]@} @{<C.G_Green>I decide@} on %a@]@." F.print f

  let backtracking f = 
    if debug_sat then 
      printf "@[@{<C.Bold>[sat]@} @{<C.G_Green>I backtrack@} on %a@]@." 
	F.print f

  let backjumping f = 
    if debug_sat then 
      (printf "@[@{<C.Bold>[sat]@} @{<C.G_Green>I don't consider the case @}";
       printf "%a@]@." F.print f)
       
  let elim _ _ = if debug_sat && verbose then printf "@[@{<C.Bold>[elim]@}@."

  let red _ _ = if debug_sat && verbose then printf "@[@{<C.Bold>[red]@}@."

  let delta d = 
    if debug_sat && verbose then begin
      printf "@[@{<C.Bold>[sat]@} - Delta ---------------------]@.";
      List.iter (fun (f1, f2, ex) ->
	printf "(%a or %a), %a@." F.print f1.f F.print f2.f Ex.print ex) d;
      printf "@[@{<C.Bold>[sat]@} --------------------- Delta -]@."
    end
    

end

(* matching part of the solver *)

let add_terms env s goal age lem = 
  let infos = { 
    Matching.term_age = age ; 
    term_from_goal = goal ;
    term_orig = lem ;
  }
  in
  { env with matching = Term.Set.fold (M.add_term infos) s env.matching }

(*exception EnoughLemmasAlready of int * (gformula * Ex.t) list*)

exception EnoughLemmasAlready of t * int

let b_max_size = 100

let rec double_until min s =
  let s2 = s + b_max_size in 
    if s2 >= min then s2 else double_until min s2

let mtriggers env formulas max_size = 
  let stop = ref false in
  try
    MF.fold
      (fun lem (age, dep) (env, max_size) ->
	 let size = F.size lem in
	 let max_size = 
	   if size <= max_size then max_size 
	   else 
	     begin
	       if !stop then raise (EnoughLemmasAlready(env, max_size));
	       stop:=true; double_until size max_size
	     end
	 in
	 let env = 
	   match F.view lem with
	       F.Lemma {F.triggers = tgs; main = f} -> 
		 List.fold_left 
		   (fun env tg ->
		      let info = 
			{ Matching.pat_age = age ; 
			  pat_orig = lem ;
			  pat_formula = f ;
			  pat_dep = dep }
		      in
		      { env with 
			  matching = 
			  M.add_pat (info, tg) env.matching env.tbox })
		   env tgs
	     | _ -> assert false		 
	 in 
	 (env, max_size)
      )
      formulas (env, max_size)
  with EnoughLemmasAlready(env, max_size) -> env, max_size

let new_facts mode env = 
  List.fold_left
    (fun acc ({Matching.pat_formula=f; 
	       pat_age=age; pat_dep=dep }, subst_list) ->
       List.fold_left
	 (fun acc {Matching.sbt=s;gen=g;goal=b} ->
	    if mode && not b then acc
	    else
	      begin
		let nf = F.apply_subst s f in
		if MF.mem nf env.gamma then acc else
		  let p = {f=nf;age=1+(max g age);name=Some f;mf=true;gf=b} in
		  (p,dep)::acc
	      end
	 ) 
	 acc subst_list
    )
    [] (M.query env.matching env.tbox)


let mround predicate mode env max_size =
  let round mode =
    Print.mround max_size;
    let axioms = if predicate then env.definitions else env.lemmas in
    let env, max_size = mtriggers env axioms max_size in
    let rec bouclage n (env, lf) = 
      if n <=0 then (env, lf)
      else 
        let env = 
	  List.fold_left 
	    (fun env (f,_) -> add_terms env (F.terms f.f) mode f.age None)
	    env lf
        in
        bouclage (n-1) (env, (new_facts mode env))
    in
    let _, lf = bouclage Options.bouclage (env, []) in
    max_size, lf 
  in
  let max_size, lf = round (mode || Options.goal_directed) in 
  if Options.goal_directed && lf = [] then round false 
  else max_size, lf
  

let extract_model t = 
  let s = ref SF.empty in
  MF.iter 
    (fun f _ -> 
       let lbl = F.label f in
       if not (Hstring.equal Hstring.empty lbl) then
	 s := SF.add f !s
    ) 
    t.gamma;
  !s

let print_model fmt s = 
  SF.iter (fprintf fmt "%a\n" F.print) s

(* sat-solver *)

let elim {f=f} env = 
  MF.mem f env.gamma ||
    match F.view f with 
      | F.Literal a -> CcX.query a env.tbox <> No
      | _ -> false

let size_formula = 1_000_000

let red {f=f} env = 
  let nf = F.mk_not f in
  try 
    Yes (MF.find nf env.gamma)
  with Not_found -> 
    match F.view nf with
      |	F.Literal a -> CcX.query a env.tbox
      | _ -> No

let pred_def env f = 
  let ff = {f=f;age=0;name=None;mf=false;gf=false} in
  Print.assume ff Explanation.empty;
  { env with definitions = MF.add f (0,Ex.empty) env.definitions }

let rec assume env ({f=f;age=age;name=lem;mf=mf;gf=gf} as ff ,dep) =
  try
    let dep = match F.view f with 
	| F.Clause _ | F.Lemma _ | F.Literal _ when proof -> 
	  if not (Ex.mem f dep) then Ex.union (Ex.singleton ~bj:false f) dep
	  else dep
	| _ -> dep
    in
    (try raise (IUnsat (Ex.union dep (MF.find (F.mk_not f) env.gamma)))
     with Not_found -> ());
    if MF.mem f env.gamma then env
    else 
      begin
	let size = F.size f in
	if size > size_formula then env
	else
	  let env =
	    if mf && glouton  && size < size_formula then 
	      add_terms env (F.terms f) gf age lem else env in
	  let env = { env with gamma = MF.add f dep env.gamma } in
	  Print.assume ff dep;
	  match F.view f with
	    | F.Unit l -> 
		List.fold_left assume env 
		  (List.map (fun x->
		    { f = x; age = age; name = lem; mf = mf; gf = gf }, dep
		   ) l)

	    | F.Clause(f1,f2) -> 
	        (* let dep = Ex.union (Ex.singleton ~bj:false f) dep in *)
		let p1 = {f=f1;age=age;name=lem;mf=mf;gf=gf} in
		let p2 = {f=f2;age=age;name=lem;mf=mf;gf=gf} in
		bcp { env with delta = (p1,p2,dep)::env.delta }

	    | F.Lemma _ ->
	        (* let dep = Ex.union (Ex.singleton ~bj:false f) dep in *)
		let age , dep = 
		  try 
		    let age' , dep' = MF.find f env.lemmas in
		    min age age' , Ex.union dep dep' 
		  with Not_found -> age , dep 
		in
		bcp { env with lemmas=MF.add f (age,dep) env.lemmas }

	    | F.Literal a ->
	        (* let dep = Ex.union (Ex.singleton ~bj:false f) dep in *)
		let env = 
		  if mf && size < size_formula then 
		    add_terms env (A.LT.terms_of a) gf age lem
		  else env 
		in
		let tbox, cpt = CcX.assume a dep env.tbox in
		steps := Int64.add (Int64.of_int cpt) !steps;
		let env = { env with tbox = tbox } in
		bcp env

	    | F.Skolem{F.ssubst=s;ssubst_ty=s_ty;sf=f} -> 
		let f' = F.apply_subst (s,s_ty) f in
		assume env ({f=f';age=age;name=lem;mf=mf;gf=gf},dep)

            | F.Let {F.lvar=lvar;lterm=lterm;lsubst=lsubst;lf=lf} ->
                let f' = F.apply_subst (lsubst,Ty.esubst) lf in
		let id = F.id f' in
                let v = Symbols.Map.find lvar lsubst in
                let env = assume env 
		  ({f=F.mk_lit (A.LT.make (A.Eq(v,lterm))) id;
		    age=age;name=lem;mf=mf;gf=gf},dep) 
		in
                assume env ({f=f';age=age;name=lem;mf=mf;gf=gf},dep)
      end
  with Exception.Inconsistent expl -> 
    if debug_sat then fprintf fmt "inconsistent %a@." Ex.print expl; 
    raise (IUnsat expl)
    
and bcp env =
  let cl , u = 
    List.fold_left 
      (fun (cl,u) ((f1,f2,d) as fd) -> 
         Print.elim f1 f2;
	 if elim f1 env || elim f2 env  then (cl,u)
	 else 
           (Print.red f1 f2;
	   match red f1 env with
	     | Yes d1 -> (cl,(f2,Ex.union d d1)::u)
	     | No -> 
		 match red f2 env with
		     Yes d2 -> (cl,(f1,Ex.union d d2)::u)
		   | No -> fd::cl , u)
      ) ([],[]) env.delta
  in
  List.fold_left assume {env with delta=cl} u
    
let rec unsat_rec env fg stop max_size = 
  try
    if stop < 0 then raise I_dont_know;
    back_tracking (assume env fg) stop max_size
  with IUnsat d-> Print.unsat (); d

and back_tracking env stop max_size =  match env.delta with
    []  when stop >= 0  -> 
      let _ , l2 = mround true false env max_max_size in 
      let env = List.fold_left assume env l2 in

      let max_size , l1 = mround false false env max_size in 
      let env = List.fold_left assume env l1 in

      let env = 
	List.fold_left 
	  (fun env ({f=f; age=g; name=lem; gf=gf},_) -> 
	     add_terms env (F.terms f) gf g lem) env l1 
      in
      (match l1, l2 with
	 | [], [] -> 
	     let m = extract_model env in
	     if all_models then 
	       begin
		 Format.printf "--- SAT ---\n";
		 Format.printf "%a@." print_model m;
		 raise (IUnsat (Ex.make_deps m))
	       end;
	     raise (Sat env)
	 | l1, l2 -> 
	     back_tracking 
	       (List.fold_left assume  (List.fold_left assume env l2) l1) 
	       (stop-1) (max_size + b_max_size))
  | [] -> 
      raise I_dont_know
  | ({f=f;age=g;name=lem;mf=mf} as a,b,d)::l -> 
      Print.decide f;
      let dep = unsat_rec {env with delta=l} (a,Ex.singleton f) stop max_size in
      if debug_sat then fprintf fmt "unsat_rec : %a@." Ex.print dep;
      try
	let dep' = Ex.remove f dep in
	Print.backtracking (F.mk_not f);
	unsat_rec
	  (assume {env with delta=l} (b, Ex.union d dep'))
	  ({a with f=F.mk_not f},dep') stop max_size
      with Not_found -> Print.backjumping (F.mk_not f); dep 
	
let unsat env fg stop = 
  try
    let env = assume env (fg,Ex.empty) in
    let env = add_terms env (F.terms fg.f) fg.gf fg.age fg.name in

    let _ , l = mround true false env max_max_size in
    let env = List.fold_left assume env l in

    let _ , l = mround false true env max_max_size in
    let env = List.fold_left assume env l in

    back_tracking env stop 100
  with IUnsat dep -> Print.unsat ();dep

let assume env fg = 
  try assume env (fg,Ex.empty) with IUnsat d -> raise (Unsat d)

let empty = { 
  gamma = MF.empty;
  delta = [] ;
  tbox = CcX.empty (); 
  lemmas = MF.empty ; 
  matching = M.empty;
  definitions = MF.empty
} 

let start () = steps := 0L
let stop () = !steps
