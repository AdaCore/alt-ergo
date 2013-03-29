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

module T = Term
module F = Formula

type gsubst = { 
  sbs : T.t Subst.t;
  sty : Ty.subst;
  gen : int ;     (* l'age d'une substitution est l'age du plus vieux 
		     terme qu'elle contient *)
  goal : bool;    (* vrai si la substitution contient un terme ayant un lien 
		     avec le but de la PO *)
  s_term_orig : Term.t list;
  s_lem_orig : Formula.t;
}

type trigger_info = {
  trigger_query : Literal.LT.t option ; 
  trigger_age : int ; (* age d'un trigger *)
  trigger_orig : Formula.t ; (* lemme d'origine *)
  trigger_formula : Formula.t ; (* formule associee au trigger *)
  trigger_dep : Explanation.t ;
}

type term_info = {
  term_age : int ;   (* age du terme *)
  term_from_goal : bool ; (* vrai si le terme provient du but de la PO *)
  term_from_formula : Formula.t option; (* lemme d'origine du terme *)
  term_from_terms : Term.t list;
}

module type X = sig
  type t

  val class_of : t -> Term.t -> Term.t list
  val query : Literal.LT.t -> t -> Sig.answer

end

module type S = sig
  type t
  type uf

  val empty : t
  val add_term : term_info -> Term.t -> t -> t 
  val add_trigger : trigger_info -> Term.t list -> t -> t
  val query : t -> uf -> (trigger_info * gsubst list) list  
end

module Make (X : X) = struct

  type uf = X.t

  module MT = T.Map

  type info = {
    age : int ; (* age du terme *)
    lem_orig : F.t list ; (* lemme d'ou provient eventuellement le terme *)
    t_orig : Term.t list; 
    but : bool  (* le terme a-t-il un lien avec le but final de la PO *)
  }

  type t = { 
    fils : T.t list MT.t Subst.t ; 
    info : info MT.t ; 
    pats : (trigger_info * Term.t list) list 
  }

  exception Echec
    
  module SubstT = Subst.Make(T)

  let empty = { 
    fils = SubstT.empty ; 
    info = MT.empty ;
    pats = [ ];
  }

  let age_limite = Options.age_limite
    (* l'age limite des termes, au dela ils ne sont pas consideres par le
       matching *)

  let infos op_gen op_but t g b env = 
    try 
      let i = MT.find t env.info in
      op_gen i.age g , op_but i.but b 
    with Not_found -> g , b

  let add_term info t env =
    (*eprintf ">>>> %d@." (MT.cardinal env.info);*)
    !Options.timer_start Timers.TMatch;
    let rec add_rec env t = 
      if MT.mem t env.info then env
      else
	let {T.f=f; xs=xs} = T.view t in
	let env = 
	  let map_f = try SubstT.find f env.fils with Not_found -> MT.empty in
	  
	  (* - l'age d'un terme est le min entre l'age passe en argument
	     et l'age dans la map 
	     - un terme est en lien avec le but de la PO seulement s'il
	     ne peut etre produit autrement (d'ou le &&)
	     - le lemme de provenance est le dernier lemme
	  *)
	  let g, b = infos min (&&) t info.term_age info.term_from_goal env in
	  let from_lems = 
	    List.fold_left 
	      (fun acc t ->
		 try (MT.find t env.info).lem_orig @ acc
		 with Not_found -> acc) 
	      (match info.term_from_formula with None -> [] | Some a -> [a]) 
	      info.term_from_terms
	  in
	  (*eprintf "[Matching.add_term] %a : " Term.print t;
	  List.iter (eprintf "%a " Formula.print) from_lems;
	  eprintf "@.";*)
	  { env with
	      fils = SubstT.add f (MT.add t xs map_f) env.fils; 
	      info = 
	      MT.add t 
		{ age=g; lem_orig = from_lems; but=b; 
	          t_orig = info.term_from_terms } 
		env.info 
	  }
	in
	List.fold_left add_rec env xs
    in
    let env = if info.term_age > age_limite () then env else add_rec env t in
    !Options.timer_pause Timers.TMatch;
    env
      
  let add_trigger p trs env = { env with pats = (p, trs) ::env.pats }

  module Debug = struct
      
    let matching pats = 
      if dmatching then begin
        fprintf fmt "[matching] (multi-)triggers: ";
        List.iter (fprintf fmt "%a , " T.print) pats;
        fprintf fmt "@.";
      end
          
    let match_pats_modulo pat lsubsts = 
      if dmatching then begin
        fprintf fmt "@.match_pat_modulo: %a  with accumulated substs@."
          T.print pat;
        List.iter (fun {sbs=sbs; sty=sty} ->
          fprintf fmt ">>> sbs= %a | sty= %a@." 
            SubstT.print sbs Ty.print_subst sty
        )lsubsts
      end
          
    let match_one_pat {sbs=sbs; sty=sty} pat0 = 
      if dmatching then
        fprintf fmt "@.match_pat: %a  with subst:  sbs= %a | sty= %a @."
          T.print pat0 SubstT.print sbs Ty.print_subst sty

    let match_term {sbs=sbs; sty=sty} t pat =
      if dmatching then 
        fprintf fmt 
          "[match_term] I match %a against %a with subst: sbs=%a | sty= %a@."
          T.print pat T.print t SubstT.print sbs Ty.print_subst sty

    let match_list {sbs=sbs; sty=sty} pats xs =
      if dmatching then 
        fprintf fmt 
          "@.[match_list] I match %a against %a with subst: sbs=%a | sty= %a@."
          T.print_list pats T.print_list xs SubstT.print sbs Ty.print_subst sty

    let match_class_of t cl =
      if dmatching then 
        fprintf fmt "class_of (%a)  = { %a }@."
          T.print t
          (fun fmt -> List.iter (fprintf fmt "%a , " T.print)) cl

  end

  exception Deja_vu
  let deja_vu lem1 lems = 
    List.exists (fun lem2 -> F.compare lem1 lem2 = 0) lems

  let matching_loop_bound = 5

  module HF = Hashtbl.Make(F)
  let matching_loop lems orig =
    List.length lems > 3*matching_loop_bound ||
    match lems with
      | [] | [_] -> false
      | f :: l -> 
	  let h = HF.create 17 in
	  HF.add h f (ref 1);
	  let max, _ = 
	    List.fold_left 
	      (fun ((max, _) as acc) f -> try 
		 let m = HF.find h f in
		 incr m;
		 if !m > max then (!m, f) else acc
	       with Not_found -> HF.add h f (ref 1); acc)
	      (1, f) l
	  in 
	  max > matching_loop_bound 

  let all_terms 
      f ty env pinfo 
      {sbs=s_t; sty=s_ty; gen=g; goal=b; 
       s_term_orig=s_torig; 
       s_lem_orig = s_lorig} lsbt_acc = 
    SubstT.fold 
      (fun k s l -> 
	 MT.fold 
	   (fun t _ l -> 
	      try
		let lems = 
		  try (MT.find t env.info).lem_orig with Not_found -> []
		in
		if matching_loop lems pinfo.trigger_orig then l
		else
		  let s_ty = Ty.matching s_ty ty (T.view t).T.ty in
		  let ng , but = 
		    try 
		      let {age=ng;lem_orig=lem'; but=bt} = MT.find t env.info in
		      if deja_vu pinfo.trigger_orig lem' then raise Deja_vu;
		      max ng g , bt or b
		    with Not_found -> g , b
		  in
		  { sbs = SubstT.add f t s_t;
		    sty = s_ty;
		    gen = ng; 
		    goal = but;
		    s_term_orig = t :: s_torig;
		    s_lem_orig = s_lorig
		  }::l
	      with Ty.TypeClash _ | Deja_vu-> l
	   ) s l
      ) env.fils lsbt_acc

  let add_msymb uf f t ({sbs=s_t; sty=s_ty} as sg)= 
    try 
      let a = Literal.LT.make (Literal.Eq (t, SubstT.find f s_t)) in
      if X.query a uf = Sig.No then raise Echec;
      sg 
    with Not_found ->  {sg with sbs=SubstT.add f t s_t; sty=s_ty}

  let (-@) l1 l2 =
    match l1, l2 with
    | [], _  -> l2
    | _ , [] -> l1
    | _ -> List.fold_left (fun acc e -> e :: acc) l2 (List.rev l1)

  let rec match_term env uf ( {sbs=s_t; sty=s_ty;gen=g;goal=b} as sg) pat t =
    !Options.thread_yield ();
    Debug.match_term sg t pat;
    let {T.f=f_pat;xs=pats;ty=ty_pat} = T.view pat in
    match f_pat with
      |	Symbols.Var _ -> 
	  let sb =
            (try
	       let s_ty = Ty.matching s_ty ty_pat (T.view t).T.ty in
	       let g',b' = infos max (||) t g b env in
	       add_msymb uf f_pat t 
		 { sg with sbs=s_t; sty=s_ty; gen=g'; goal=b' }
	     with Ty.TypeClash _ -> raise Echec)
          in 
          [sb]
      | _ -> 
        try
          let s_ty = Ty.matching s_ty ty_pat (T.view t).T.ty in
          let cl = X.class_of uf t in
          Debug.match_class_of t cl;
          let cl =
	    List.fold_left
	      (fun l t -> 
                let {T.f=f; xs=xs} = T.view t in
	        if Symbols.compare f_pat f = 0 then xs::l else l
	      )[] cl
          in
          let gsb = { sg with sbs = s_t; sty = s_ty } in
          (* pas sur que ce soit correct ici *)
          List.fold_left
            (fun acc xs -> 
              try (match_list env uf gsb pats xs) -@ acc
              with Echec -> acc
            ) [] cl
        with Ty.TypeClash _ -> raise Echec

  and match_list env uf sg pats xs = 
    Debug.match_list sg pats xs;
    try 
      List.fold_left2 
        (fun sb_l pat arg -> 
           List.fold_left 
             (fun acc sg -> 
                let aux = match_term env uf sg pat arg in
                match aux with [] -> raise Echec | _  -> List.rev_append aux acc
             ) [] sb_l
        ) [sg] pats xs 
    with Invalid_argument _ -> raise Echec

  let match_one_pat env uf pat_info pat0 lsbt_acc sg =
    Debug.match_one_pat sg pat0;
    let pat = T.apply_subst (sg.sbs, sg.sty) pat0 in
    let {T.f=f; xs=pats; ty=ty} = T.view pat in
    match f with
      | Symbols.Var _ -> all_terms f ty env pat_info sg lsbt_acc
      | _ -> 
        let {sty=sty; gen=g; goal=b} = sg in
        let f_aux t xs lsbt = 
	  let lems = try (MT.find t env.info).lem_orig with Not_found -> [] in
	  if matching_loop lems pat_info.trigger_orig then lsbt
	  else
	    try
	      let s_ty = Ty.matching sty ty (T.view t).T.ty in
	      let gen, but = infos max (||) t g b env in
              let sg =
                { sg with 
                  sty = s_ty; gen = gen; goal = but; 
                  s_term_orig = t::sg.s_term_orig }
              in
	      let aux = match_list env uf sg pats xs in
              List.rev_append aux lsbt
	    with Echec | Ty.TypeClash _ -> lsbt
        in
	try MT.fold f_aux (SubstT.find f env.fils) lsbt_acc
	with Not_found -> lsbt_acc

  let match_pats_modulo env uf pat_info lsubsts pat = 
    Debug.match_pats_modulo pat lsubsts;
    List.fold_left (match_one_pat env uf pat_info pat) [] lsubsts
      
  let matching env uf (pat_info, pats) =
    Debug.matching pats;
    let egs = 
      { sbs = SubstT.empty;
        sty = Ty.esubst; 
        gen = 0; 
	goal = false; 
	s_term_orig = [];
	s_lem_orig = pat_info.trigger_orig;
      } 
    in
    pat_info, List.fold_left (match_pats_modulo env uf pat_info) [egs] pats

  let query env uf = 
    !Options.timer_start Timers.TMatch;
    let res = List.rev_map (matching env uf) env.pats in
    !Options.timer_pause Timers.TMatch;
    res

end
