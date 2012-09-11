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

open Format
open Options

module T = Term
module F = Formula

type 'a trigger_info = { 
  trigger_orig : 'a; (* lemme d'origine *)
  trigger_formula : 'a; (* formule associee au trigger *)
  trigger_dep : Explanation.t;
}


module Make (Uf : Uf.S) (Use : Use.S with type r = Uf.R.r) = struct

  let debug = false

  module MT = T.Map
    
  module SubstT = Subst.Make(T)

  module IMap = Map.Make (struct type t = int let compare = compare end)

  module RMap = Map.Make (struct type t = Uf.R.r let compare = Uf.R.compare end)

  (* A path_index is a tree. Edges are marked by a symbol and nodes contain
     a list of elements. Elements are couples (id, num) where id is the
     identifier of a formula f and num the number of a specific trigger
     of f. *)
  type path_index = Path of path_index Symbols.Map.t * (int * int) list

  let rec print_path fmt p = 
    let Path (path, leafs) = p in
    fprintf fmt "Leafs: %i@." (List.length leafs);
    Symbols.Map.iter (fun sy p ->
      fprintf fmt "[[%a -> %a]]@." Symbols.print sy print_path p) path

  let empty_path = Path (Symbols.Map.empty, [])

  let parents (uf, use) t =
    let r, _ = Uf.find uf t in
    let s, _ = Use.find r use in
    s

  (* Collects (t, (id, num)) where there is a path s1...sn leading to (id, num)
     in p such that there is a known term s1 (... sn (..., term, ...) ...) *)
  let rec collect uf term acc p =
    let Path (path, leafs) = p in
    let acc = List.fold_left (fun acc v -> (term, v) :: acc) acc leafs in
    T.Set.fold (fun t acc ->
      let { Term.f = s } = Term.view t in
      try let p = Symbols.Map.find s path in
          collect uf t acc p
      with Not_found -> acc) (parents uf term) acc

  (* adds a path symbols leading to an element v to p *)
  let rec add symbols v p =
    let Path (path, leafs) = p in
    match symbols with
      | [] -> Path (path, v :: leafs)
      | sy :: symbols ->
        let p = try Symbols.Map.find sy path with
            Not_found -> empty_path in
        let p = add symbols v p in
        Path (Symbols.Map.add sy p path, leafs)

  type 'a t = { fils : T.t list MT.t Subst.t; (* s -> t -> [t1 ... tn]
                                                 t = s (t1 ... tn) is known *)
                info : Explanation.t MT.t; (* Explanation of known terms *)
                pats : 'a trigger_info IMap.t; (* Triggers *)
                seen : (T.t list * (T.subst * Explanation.t) list)
                  IMap.t IMap.t; (* id -> num -> (triggers * (subst * exp)) *)
                funs : Symbols.Set.t RMap.t; (* function symbols starting
                                                terms in an eq class *)
                pp : path_index; (* path for pp pairs *)
                pc : path_index Symbols.Map.t; (* path for pc pairs *)
                count : int }

  type 'a result = ('a trigger_info * (Term.subst * Explanation.t) list) list

  let empty = { fils = SubstT.empty; 
                info = MT.empty; 
                pats = IMap.empty;
                seen = IMap.empty;
                funs = RMap.empty;
                pp = empty_path;
                pc = Symbols.Map.empty;
                count = 0 }

  exception Echec

  (* over-approximation of (t', (id, num)) such that t' matches the trigger
     num of formula id because t' = f1 (... fn (... t1 ...) ...),
     t2 = g1 (...) and t1 = t2 = t *)
  let find_pc acc env uf t funs =
    let res = Symbols.Set.fold (fun s acc ->
      try (let path = Symbols.Map.find s env.pc in
           if debug then 
             fprintf fmt "path from %a:\n %a@." Symbols.print s print_path path;
           collect uf t acc path)
      with Not_found -> acc) funs acc in
    if debug then 
      List.iter (fun (t, _) -> fprintf fmt "New term: %a@." Term.print t) res;
    res

  (* over-approximation of (t', (id, num)) such that t' matches the trigger
     num of formula id because t' = f1 (... fn (... t1 ...) ... fm (... t2 ...))
     and t1 = t2 = t *)
  let find_pp acc env uf t =
    collect uf t acc env.pp

  (* terms that should be checked when t's equivalence class is updated *)
  let to_check env uf t funs =
    if debug then (fprintf fmt "Merge %a@." T.print t;
                   Symbols.Set.iter (fprintf fmt "%a " Symbols.print) funs;
                   fprintf fmt "@.");
    find_pc (find_pp [] env uf t) env uf t funs

  let rec update_paths v l (seen, (lpp, lpc)) t =
      let { T.f = s; T.xs = xs } = T.view t in
      match s with
	  Symbols.Var _ ->
            if T.Set.mem t seen then
              (seen, ((v, l) :: lpp, lpc))
            else
              (T.Set.add t seen, (lpp, lpc))
        | _ -> 
          let lpc = (v, s :: l) :: lpc in
          List.fold_left (update_paths v (s :: l)) (seen, (lpp, lpc)) xs

  (* updates pp and pc pairs when a new quantified formula is assumed *)
  let update_paths id trs (pp, pc) =
    let (_, (lpp, lpc)), _ = List.fold_left (fun (acc, c) t ->
      update_paths (id, c) [] acc t, c+1) ((T.Set.empty, ([], [])), 0) trs in
    let pp = List.fold_left (fun pp (v, l) -> if l = [] then pp
      else add l v pp) pp lpp in
    let pc = List.fold_left (fun pc (v, l) ->
      match l with
        | a :: ((_ :: _) as l) ->
          let p = try Symbols.Map.find a pc with Not_found -> empty_path in
          let p = add l v p in
          Symbols.Map.add a p pc
        | _ -> pc (* ignore variables and constants *)) pc lpc in
    (pp, pc)

  (************************************************************************)

  let infos t ex env = 
    try 
      MT.find t env.info
    with Not_found -> ex

  let all_terms f ty env terms (s_t,s_ty) lsbt_acc ex = 
    SubstT.fold 
      (fun k s l -> 
	 MT.fold 
	   (fun t _ (lsbt, seen) -> 
	      try
		let s_ty = Ty.matching s_ty ty (T.view t).T.ty in
		let ex = Explanation.union (MT.find t env.info) ex in
                let s = (SubstT.add f t s_t, s_ty) in
                if List.mem_assoc s seen then (lsbt, seen)
                else (s, ex) :: lsbt, (s, ex) :: seen
	      with Ty.TypeClash _  -> lsbt, seen
	   ) s l
      ) terms lsbt_acc

  let add_msymb uf f t (s_t,s_ty) = 
    try 
      let t' = SubstT.find f s_t in
      if Uf.are_equal uf t t' <> Sig.No
      then (s_t,s_ty)
      else raise Echec
    with Not_found ->  SubstT.add f t s_t,s_ty

  let rec iter_exception f gsb l =
    let l = 
      List.fold_left
        (fun acc xs -> try (f gsb xs) @ acc with Echec -> acc) [] l in
    match l with [] -> raise Echec | l  -> l

  (* computes the substitution(s) containing (st,sty) such that pat = t *)
  let rec matchterm uf (s_t,s_ty) pat (t, ex) =
    let {T.f=f_pat;xs=pats;ty=ty_pat} =  T.view pat in
    match f_pat with
	Symbols.Var _ -> 
	  let sb =
            (try
	       let s_ty = Ty.matching s_ty ty_pat (T.view t).T.ty in
	       add_msymb uf f_pat t (s_t,s_ty)
	     with Ty.TypeClash _ -> raise Echec)
          in 
          [sb, ex]
      | _ -> 
	let l = Uf.class_of uf t in
	let s_ty, l = 
	  List.fold_left
	    (fun (s_ty,l) t' -> 
              let {T.f=f; ty=ty_t} as v = T.view t' in
	      if Symbols.compare f_pat f = 0 then 
		try
		  let s_ty = Ty.matching s_ty ty_pat ty_t in
                  match Uf.are_equal uf t t' with
                    | Sig.No -> assert false
                    | Sig.Yes (r, _) -> s_ty , (v, Explanation.union r ex)::l 
		with Ty.TypeClash _ -> s_ty , l
	      else s_ty , l
	    ) (s_ty,[]) l 
	in
	iter_exception
	  (fun m ({T.xs=xs}, ex) -> matchterms uf m pats xs ex) 
	  (s_t,s_ty) l

  (* computes the substitution(s) containing (st,sty) such that pat1 = t1,
     pat2 = t2, ... *)
  and matchterms uf sg pats xs ex = 
    try 
      List.fold_left2 
        (fun sb_l pat arg -> 
           List.fold_left 
             (fun acc (sg, ex) -> 
                let aux = matchterm uf sg pat (arg, ex) in
                List.rev_append aux acc) [] sb_l
        ) [sg, ex] pats xs 
    with Invalid_argument _ -> raise Echec

  (* computes the substitution(s) containing (st,sty) such that pat is in 
     terms. Do not return sustitutions already in seen *)
  let matchpat env terms uf (lsbt_acc, seen) ((st,sty), pat) ex = 
    let {T.f=f;xs=pats;ty=ty} = T.view pat in
    match f with
      |	Symbols.Var _ -> all_terms f ty env terms (st,sty) (lsbt_acc, seen) ex
      | _ -> 
	  try  
	    MT.fold 
	      (fun t xs lsbt ->
		try
		  let s_ty = 
		    try Ty.matching sty ty (T.view t).T.ty 
		    with Ty.TypeClash _ -> sty in
		  let ex = Explanation.union ex 
                    (infos t Explanation.empty env) in
		  let aux = 
                    matchterms uf (st,s_ty) pats xs ex in
                  List.fold_left (fun (lsbt, seen) (s, ex) ->
                    if List.mem_assoc s seen then (lsbt, seen)
                    else (s, ex) :: lsbt, (s, ex) :: seen) lsbt aux
		with Echec -> lsbt
              ) (SubstT.find f terms) (lsbt_acc, seen)
	  with Not_found -> lsbt_acc, seen

  let print_subst fmt l =
    if l = [] then fprintf fmt "X"
    else
      List.iter (fun ((s, _), _) -> fprintf fmt "[ ";
        Symbols.Map.iter (fun s t -> fprintf fmt "%a <- %a, "
          Symbols.print s T.print t) s;
        fprintf fmt "] ") l

  let print_terms fmt l =
    fprintf fmt "{ ";
    SubstT.iter (fun s t -> fprintf fmt "%a: " Symbols.print s;
      MT.iter (fun t _ -> fprintf fmt "%a, " T.print t) t) l;
    fprintf fmt "}"

  (* computes the substitution(s) containing a substitution of lsubst such that
     pat is in terms. Do not return substitutions already in seen. *)
  let matchpats env terms uf (lsubsts, seen, id) pat =
    if debug then
      fprintf fmt "Pattern %a . %a in %a:@." T.print pat print_subst lsubsts
        print_terms terms;
    let tl, s = IMap.find id seen in
    let acc, s = List.fold_left (fun acc (sg, ex) ->
         matchpat env terms uf acc (sg, T.apply_subst sg pat) ex) 
      ([], s) lsubsts in
    if debug then fprintf fmt "   %a@." print_subst acc;
    (acc, IMap.add id (tl, s) seen, id + 1)
      
  (* computes every possible match for a given set of patterns with known
     terms *)
  let matching_trigger (id, info, pats) env uf = 
    let egs = (SubstT.empty,Ty.esubst) in
    let seen = IMap.find id env.seen in
    let acc = ([egs, Explanation.empty], seen, 0) in
    let acc, seen, _ = List.fold_left (matchpats env env.fils uf) acc pats in
    {env with seen = IMap.add id seen env.seen}, [info, acc]

  (* computes every possible match containing subst for a given set of patterns
     such that the first pattern is in terms *)
  let matching_term terms env uf id (pats, subst) (seen, forms) =
    match pats, subst with
      | _, [] | [], _ -> seen, forms
      | t :: pats, _ ->
        let acc = matchpats env terms uf (subst, seen, id+1) t in
        let acc, seen, _ = List.fold_left (matchpats env env.fils uf) 
          acc pats in
        seen, List.rev_append acc forms
      
  (* computes every possible match for every assumed patterns
     such that the first pattern is in terms *)
  let matching_terms terms env uf =
    IMap.fold (fun id m (env, acc) ->
      let info = IMap.find id env.pats in
      let (seen, forms) = IMap.fold (matching_term terms env uf) m (m, []) in
      {env with seen = IMap.add id seen env.seen}, (info, forms) :: acc)
      env.seen (env, [])

  (* update the environment when a term is assumed. Returns the new terms *)
  let rec add_rec ex (env, news) t = 
    if MT.mem t env.info then (env, news)
    else
      let {T.f=f;xs=xs} = T.view t in
      let map_f = try SubstT.find f env.fils with Not_found -> MT.empty in
      let new_f = try SubstT.find f news with Not_found -> MT.empty in
      let ex = infos t ex env in
      let acc = { env with
        fils = SubstT.add f (MT.add t xs map_f) env.fils; 
        info = MT.add t ex env.info }, SubstT.add f (MT.add t xs new_f) news in
      List.fold_left (add_rec ex) acc xs

  (* Assumes a new term for matching *)
  let add_term ex t env uf =
    if debug then fprintf fmt "Term %a@." T.print t;
    let env, news = add_rec ex (env, SubstT.empty) t in
    matching_terms news env uf

  let rec empty_seen pats i s =
    match pats with
      | [] -> s
      | t :: pats -> empty_seen pats (i+1) (IMap.add i (pats, []) s)

  let empty_seen pats = empty_seen pats 1
    (IMap.add 0 (pats, [(SubstT.empty,Ty.esubst), Explanation.empty])
       IMap.empty)

  (* Assumes a quantified formula with triggers *)
  let add_trigger info trs env uf =
    let count = env.count in
    let pp, pc = update_paths count trs (env.pp, env.pc) in
    let pats = IMap.add count info env.pats in
    let seen = IMap.add count (empty_seen trs) env.seen in
    let env = 
      {env with pats=pats; pp=pp; pc=pc; count=env.count+1; seen=seen} in
    matching_trigger (count, info, trs) env uf

  (* Checks wether a the pattern num of formula id can be matched with t
     to give new instances *)
  let check uf (env, acc) (t, (id, num)) =
    let seen = IMap.find id env.seen in
    let info = IMap.find id env.pats in
    let {T.f=f;xs=xs} = T.view t in
    let terms = SubstT.add f (MT.add t xs MT.empty) SubstT.empty in
    let seen, forms = matching_term terms env uf num (IMap.find num seen)
      (seen, []) in
    {env with seen=IMap.add id seen env.seen}, (info, forms)::acc

  (* Merges the equivalence classes of r1 and r2.
     Uses to_check to find an over-approximation of possible new matches
     and checks each of them for new instances. *)
  let merge r1 r2 t env (uf, use) =
    let funs = try
      let f1 = RMap.find r1 env.funs in
      let f2 = RMap.find r2 env.funs in
      Symbols.Set.union f1 f2
      with Not_found ->
      List.fold_left (fun v t ->
        let { T.f = s } = T.view t in
        Symbols.Set.add s v) Symbols.Set.empty (Uf.class_of uf t) in
    let env = {env with funs = RMap.add r2 funs env.funs} in
    let checks = to_check env (uf, use) t funs in
    List.fold_left (check uf) (env, []) checks

end
