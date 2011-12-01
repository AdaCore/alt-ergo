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
  
module Sy = Symbols
module T  = Term
module A  = Literal
module L  = List
  
type 'a abstract = unit

module type ALIEN = sig
  include Sig.X
  val embed : r abstract -> r
  val extract : r -> (r abstract) option
end

module Make(X : ALIEN) = struct

  type t = X.r abstract
  type r = X.r

  let name           = "Farrays"
  let unsolvable _   = assert false 
  let is_mine_a _    = false
  let is_mine_symb _ = false
  let fully_interpreted sb = assert false
  let is_mine_type _ = false
  let type_info _    = assert false
  let color _        = assert false
  let print _ _      = assert false
  let embed _        = assert false
  let compare _ _    = assert false
  let hash _         = assert false
  let leaves _       = assert false
  let subst _ _ _    = assert false 
  let make _         = assert false
  let solve _ _    = assert false


  module Rel = struct

    open Sig
    module Ex = Explanation

    type r = X.r
    
    module LR = Literal.Make(struct type t = X.r include X end)
    
    (* map get |-> { set } des associations (get,set) deja splites *)
    module Tmap = struct
      include T.Map
      let update t a mp = 
        try add t (T.Set.add a (find t mp)) mp
        with Not_found -> add t (T.Set.singleton a) mp
      let splited t a mp = try T.Set.mem a (find t mp) with Not_found -> false
    end
      
    module LRset= LR.Set

    module Conseq = 
      Set.Make
        (struct
           type t = A.LT.t * Ex.t
           let compare (lt1,_) (lt2,_) = A.LT.compare lt1 lt2
         end)
    (* map k |-> {sem Atom} d'egalites/disegalites sur des atomes semantiques*)
    module LRmap = struct
      include LR.Map
      let find k mp = try find k mp with Not_found -> Conseq.empty
      let add k v ex mp = add k (Conseq.add (v,ex) (find k mp)) mp
    end

    type gtype = {g:Term.t; gt:Term.t; gi:Term.t; gty:Ty.t}
    module G :Set.S with type elt = gtype = Set.Make
      (struct type t = gtype let compare t1 t2 = T.compare t1.g t2.g end)

    (* ensemble de termes "set" avec leurs arguments et leurs types *)
    type stype = {s:T.t; st:T.t; si:T.t; sv:T.t; sty:Ty.t}
    module S :Set.S with type elt = stype = Set.Make
      (struct type t = stype let compare t1 t2 = T.compare t1.s t2.s end)

    (* map t |-> {set(t,-,-)} qui associe a chaque tableau l'ensemble 
       de ses affectations *)
    module TBS = struct
      include Map.Make(T)
      let find k mp = try find k mp with Not_found -> S.empty
        
      (* add reutilise find ci-dessus *)
      let add k v mp = add k (S.add v (find k mp)) mp
    end

    type t = 
        {gets  : G.t;               (* l'ensemble des "get" croises*)
         tbset : S.t TBS.t ;        (* map t |-> set(t,-,-) *)
         split : LRset.t;           (* l'ensemble des case-split possibles *)
         conseq   : Conseq.t LRmap.t; (* consequences des splits *)
         seen  : T.Set.t Tmap.t;    (* combinaisons (get,set) deja splitees *)
	}
          

    let empty _ = 
      {gets  = G.empty;
       tbset = TBS.empty;
       split = LRset.empty;
       conseq   = LRmap.empty;
       seen  = Tmap.empty}

    module Debug = struct

      let assume fmt la = 
        if debug_arrays && la <> [] then begin
          fprintf fmt "[Arrays.Rel] We assume@.";
          L.iter (fun (a,_,_) -> fprintf fmt "  > %a@." 
                    LR.print (LR.make a)) la;
        end

      let print_gets fmt = G.iter (fun t -> fprintf fmt "%a@." T.print t.g)
      let print_sets fmt = S.iter (fun t -> fprintf fmt "%a@." T.print t.s)
      let print_splits fmt = 
        LRset.iter (fun a -> fprintf fmt "%a@." LR.print a)
      let print_tbs fmt = 
        TBS.iter (fun k v -> fprintf fmt "%a --> %a@." T.print k print_sets v)

      let env fmt env = 
        if debug_arrays then begin
          fprintf fmt "-- gets ----------------------------------------@.";
          print_gets fmt env.gets;
          fprintf fmt "-- tabs of sets --------------------------------@.";
          print_tbs fmt env.tbset;
          fprintf fmt "-- splits --------------------------------------@.";
          print_splits fmt env.split;
          fprintf fmt "------------------------------------------------@."
        end

      let new_equalities fmt st = 
        if debug_arrays then 
          begin
            fprintf fmt "[Arrays] %d implied equalities@." 
	      (Conseq.cardinal st);
            Conseq.iter (fun (a,ex) -> fprintf fmt "  %a : %a@."
                           A.LT.print a Ex.print ex) st
          end
    end

    (* met a jour gets et tbset en utilisant l'ensemble des termes donne*)
    let update_gets_sets st acc =
      List.fold_left
        (fun (gets,tbset) t ->
           let {T.f=f;xs=xs;ty=ty} = T.view t in 
           match Sy.is_get f, Sy.is_set f, xs with
             | true , false, [a;i]   -> 
                 G.add {g=t; gt=a; gi=i; gty=ty} gets, tbset

             | false, true , [a;i;v] -> 
                 gets, TBS.add a {s=t; st=a; si=i; sv=v; sty=ty} tbset

             | false, false, _ -> 
                 (gets,tbset)

             | _  -> assert false
        )acc st
        
    (* met a jour les composantes gets et tbset de env avec les termes 
       contenus dans les atomes de la *)
    let new_terms env la =
      let fct acc r =
        match X.term_extract r with
          | Some t -> 
              let {T.xs=xs} = T.view t in
              update_gets_sets (t::xs) acc
          | None   -> acc
      in 
      let gets, tbset = 
        L.fold_left
          (fun acc (a,_,_)->
             match a with 
               | A.Eq (r1,r2) -> fct (fct acc r1) r2
               | A.Builtin (_,_,l) | A.Distinct (_, l) -> L.fold_left fct acc l
          )(env.gets,env.tbset) la
      in 
      {env with gets=gets; tbset=tbset}

        
    (* mise a jour de env avec les instances 
       1) p   => p_ded 
       2) n => n_ded *)
    let update_env are_eq are_dist dep env acc gi si p p_ded n n_ded =
      match are_eq gi si, are_dist gi si with
        | Sig.Yes idep, Sig.No -> 
            let conseq = LRmap.add n n_ded dep env.conseq in
            {env with conseq = conseq}, 
            Conseq.add (p_ded, Ex.union dep idep) acc
              
        | Sig.No, Sig.Yes idep -> 
            let conseq = LRmap.add p p_ded dep env.conseq in
            {env with conseq = conseq},
            Conseq.add (n_ded, Ex.union dep idep) acc
              
        | Sig.No, Sig.No ->
            let sp = LRset.add p env.split in
            let conseq = LRmap.add p p_ded dep env.conseq in
            let conseq = LRmap.add n n_ded dep conseq in
            { env with split = sp; conseq = conseq }, acc
              
        | Sig.Yes _,  Sig.Yes _ -> assert false
        
    (*----------------------------------------------------------------------
      get(set(-,-,-),-) modulo egalite
      ---------------------------------------------------------------------*)
    let get_of_set are_eq are_dist gtype (env,acc) class_of = 
      let {g=get; gt=gtab; gi=gi; gty=gty} = gtype in
      L.fold_left
        (fun (env,acc) set -> 
           if Tmap.splited get set env.seen then (env,acc)
           else 
             let env = {env with seen = Tmap.update get set env.seen} in
             let {T.f=f;xs=xs;ty=sty} = T.view set in 
             match Sy.is_set f, xs with
               | true , [stab;si;sv] -> 
                   let xi, _ = X.make gi in
                   let xj, _ = X.make si in
                   let get_stab  = T.make (Sy.Op Sy.Get) [stab;gi] gty in
                   let p       = LR.make (A.Eq(xi,xj)) in
                   let p_ded   = A.LT.make (A.Eq(get,sv)) in
                   let n     = LR.make (A.Distinct(false, [xi;xj])) in
                   let n_ded = A.LT.make (A.Eq(get,get_stab)) in
                   let dep = match are_eq gtab set with
                       Yes dep -> dep | No -> assert false
                   in 
                   update_env are_eq are_dist dep env acc gi si p p_ded n n_ded
               | _ -> (env,acc)
        ) (env,acc) (class_of gtab)

    (*----------------------------------------------------------------------
      get(t,-) and set(t,-,-) modulo egalite
      ---------------------------------------------------------------------*)
    let get_and_set are_eq are_dist gtype (env,acc) class_of =
      let {g=get; gt=gtab; gi=gi; gty=gty} = gtype in
      let suff_sets = 
        L.fold_left
          (fun acc t -> S.union acc (TBS.find t env.tbset))
          S.empty (class_of gtab)
      in
      S.fold
        (fun  {s=set; st=stab; si=si; sv=sv; sty=sty} (env,acc) -> 
           if Tmap.splited get set env.seen then (env,acc)
           else 
             begin
               let env = {env with seen = Tmap.update get set env.seen} in
               let xi, _ = X.make gi in
               let xj, _ = X.make si in
               let get_stab  = T.make (Sy.Op Sy.Get) [stab;gi] gty in
               let gt_of_st  = T.make (Sy.Op Sy.Get) [set;gi] gty in
               let p       = LR.make (A.Eq(xi,xj)) in
               let p_ded   = A.LT.make (A.Eq(gt_of_st,sv)) in
               let n     = LR.make (A.Distinct(false, [xi;xj])) in
               let n_ded = A.LT.make (A.Eq(gt_of_st,get_stab)) in
               let dep = match are_eq gtab stab with
                   Yes dep -> dep | No -> assert false
               in 
               update_env are_eq are_dist dep env acc gi si p p_ded n n_ded
             end
        ) suff_sets (env,acc)
        
    (* Generer de nouvelles instantiations de lemmes *)
    let new_splits are_eq are_dist env acc class_of = 
      G.fold
        (fun gt_info accu ->
           let accu = get_of_set are_eq are_dist  gt_info accu class_of in
           get_and_set are_eq are_dist  gt_info accu class_of
        ) env.gets (env,acc)
        
    (* nouvelles disegalites par instantiation du premier
       axiome d'exentionnalite *)
    let extensionality acc la class_of =
      List.fold_left
        (fun acc (a, _, dep) ->
           match a with 
             | A.Distinct(false, [r;s]) -> 
                 begin
                   match X.type_info r, X.term_extract r, X.term_extract s with
                     | Ty.Tfarray (ty_k, ty_v), Some t1, Some t2  -> 
                         let i  = T.fresh_name ty_k in
                         let g1 = T.make (Sy.Op Sy.Get) [t1;i] ty_v in
                         let g2 = T.make (Sy.Op Sy.Get) [t2;i] ty_v in
                         let d  = A.Distinct(false, [g1;g2]) in
                         Conseq.add (A.LT.make d, dep) acc
                     | _ -> acc
                 end
             | _ -> acc
        ) acc la

    let implied_consequences env eqs la =
      let spl, eqs = 
        L.fold_left
          (fun (spl,eqs) (a,_,dep) ->
             let a = LR.make a in
             let spl = LRset.remove (LR.neg a) (LRset.remove a spl) in
             let eqs = 
               Conseq.fold
                 (fun (fact,ex) acc -> Conseq.add (fact, Ex.union ex dep) acc)
                 (LRmap.find a env.conseq) eqs 
             in
             spl, eqs
          )(env.split, eqs) la
      in
      {env with split=spl}, eqs
        
    (* deduction de nouvelles dis/egalites *)
    let new_equalities env eqs la class_of = 
      let la = L.filter 
        (fun (a,_,_) -> match a with A.Builtin _  -> false | _ -> true) la 
      in
      let eqs = extensionality eqs la class_of in
      implied_consequences env eqs la
       
    (* XXXXXX : TODO -> ajouter les explications dans les choix du
       case split *)
    (* choisir une egalite sur laquelle on fait un case-split *)
    let case_split env = 
      try
        let a = LRset.choose env.split in
        if debug_arrays then 
          fprintf fmt "[Arrays.case-split] %a@." LR.print a;
        [LR.view a, Ex.empty, Num.Int 2] 
      with Not_found ->
	if debug_arrays then fprintf fmt "[Arrays.case-split] Nothing@.";
	[]
          
    let assume env la ~are_eq ~are_neq ~class_of = 
      (* instantiation des axiomes des tableaux *)
      Debug.assume fmt la; 
       let env = new_terms env la in
      let env, atoms = new_splits are_eq are_neq env Conseq.empty class_of in
      let env, atoms = new_equalities env atoms la class_of in
      (*Debug.env fmt env;*)
      Debug.new_equalities fmt atoms;
      let l = Conseq.fold (fun (a,ex) l -> ((LTerm a, ex)::l)) atoms [] in
      env, { assume = l; remove = [] }
	  
    let query _ _ ~are_eq ~are_neq ~class_of = Sig.No
    let add env r = env

  end

  let term_extract _ = None
end
