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
open Exception
open Sig

module type S = sig
  type t

  module R : Sig.X

  val empty :  t
  val add : t -> Term.t -> t * Literal.LT.t list
  val add_semantic : t -> R.r -> t 

  val mem : t -> Term.t -> bool

  val find : t -> Term.t -> R.r * Explanation.t
  val find_r : t -> R.r -> R.r * Explanation.t
    
  val union : 
    t -> R.r -> R.r -> Explanation.t -> t * (R.r * (R.r * R.r * Explanation.t) list * R.r) list

  val distinct : t -> Term.t -> Term.t -> Explanation.t -> t

  val equal : t -> Term.t -> Term.t -> bool
  val are_distinct : t -> Term.t -> Term.t -> bool
  val class_of : t -> Term.t -> Term.t list

  val explain : t -> Term.t -> Term.t -> Explanation.t
  val neq_explain : t -> Term.t -> Term.t -> Explanation.t
  val print : Format.formatter -> t -> unit

  val distinct_r : 
    t -> R.r -> R.r -> Explanation.t -> Explanation.t -> Explanation.t -> t

  val rewrite_system : t -> (Term.t Why_ptree.rwt_rule) list -> t
    
end
  
module Make ( R : Sig.X ) = struct

  module Ac = Ac.Make(R)
  module L  = List
  module HS = Hstring
  module Ex = Explanation
  module R = R
  module Sy= Symbols
  module T = Term
  module F = Formula
  module MapT = Term.Map
  module SetT = Term.Set
  module SetF = Formula.Set
    
  let equations = Queue.create ()

  module MapR = Map.Make(struct type t = R.r let compare = R.compare end)
    
  module SetR = Set.Make(struct type t = R.r let compare = R.compare end)

  module SetAc = Set.Make(struct type t = Ac.t let compare = Ac.compare end)

  module SetRL = Set.Make
    (struct 
      type t = Ac.t * R.r
      let compare (ac1,_) (ac2,_)= Ac.compare ac1 ac2
     end)

  module RS = struct
    include Map.Make(struct type t = Sy.t let compare = Sy.compare end)
      
    let find k m = try find k m with Not_found -> SetRL.empty

    let add_rule (ac,d) m = add ac.h (SetRL.add (ac,d) (find ac.h m)) m

    let remove_rule (ac,d) m = add ac.h (SetRL.remove (ac,d) (find ac.h m)) m
  end

  (**********************************************************)
  module URS : sig
    type t
    val empty : t
    val add : t -> Term.t Why_ptree.rwt_rule -> t
    val canon : t -> (T.t -> T.t list) -> R.r -> R.r
    val canon_term : t -> (T.t -> T.t list) -> Term.t -> Term.t
  end = struct


    open Why_ptree
    open Options
    module Smap = Sy.Map
    module Tset = T.Set
    module Tmap = T.Map
    module SubstT = Subst.Make(T)

    type t = Lf of T.t * Tset.t | Nd of t Smap.t
    
    let star  = Symbols.var "*"

    let empty = Nd Smap.empty 

    module Debug = struct
      
      let prule_aux fmt (s,t) =
        fprintf fmt "%a --> %a" T.print s T.print t

      let prule fmt {rwt_left=s; rwt_right=t} = prule_aux fmt (s,t)

      let rec print_dn_aux sep fmt = function
        | Lf (_,st) -> 
          if (Tset.is_empty st) then fprintf fmt "@."
          else fprintf fmt "{%a}@." T.print_list (Tset.elements st)
        | Nd mp -> 
          fprintf fmt "@.";
          Smap.iter 
            (fun sy sb_dn -> 
              fprintf fmt "%s-(%a)->%a" 
                sep Sy.print sy (print_dn_aux (sep^"   ")) sb_dn) mp
            
            
      let print_dn fmt dn =
        fprintf fmt "@.-- Discrimination Net (lhs of rules) ---------";
        fprintf fmt "%a" (print_dn_aux "") dn;
        fprintf fmt "------------------------------------------------@."

      let print_matched l =
        fprintf fmt "@.-- Matched rules -----------------------------@.";
        List.iter
          (fun (_,_,(s,tset)) ->
            Tset.iter (fun t -> fprintf fmt "%a@." prule_aux (s,t)) tset
          )l;
        fprintf fmt "------------------------------------------------@."

    end

    let typed_string_repr t =
      let rec srepr acc t  = 
        let {T.f=f; xs=xs; ty=ty} = T.view t in
        let acc1, acc2 = L.fold_left srepr acc (L.rev xs) in
        (match f with Sy.Var _ -> f :: acc1 | _ -> acc1), ty::acc2
      in 
      srepr ([],[]) t

    (* representation applatie en pre-ordre de t *)
    let string_repr t =
      let rec srepr acc t  = 
        let {T.f=f; xs=xs; ty=ty} = T.view t in
        let acc = L.fold_left srepr acc (L.rev xs) in
        match f with Sy.Var _ -> star::acc | _ -> f::acc 
      in
      srepr [] t

      let rec dn_of s t = function
        | []    -> Lf (s, Tset.singleton t)
        | sy::r -> Nd (Smap.add sy (dn_of s t r) Smap.empty)

      let add dn ({rwt_left=s; rwt_right=t} as rwt) = 
        if verbose then fprintf fmt "[URS] add_rule %a@." Debug.prule rwt;
        let rec add_rec dn l = 
          match dn, l with
            | Lf (s,st), [] -> Lf (s, Tset.add t st)
            | Lf (_,st) , _::_  -> dn_of s t l
            | Nd mp , sy::r -> 
              let dn' = 
                try add_rec (Smap.find sy mp) r
                with Not_found -> dn_of s t r in
              Nd (Smap.add sy dn' mp)

            | _ -> assert false
        in 
        let new_dn = add_rec dn (string_repr s) in
        if verbose then fprintf fmt "%a@." Debug.print_dn new_dn;
        new_dn


      let x_query class_of t1 t2 = 
        let r1, _ = R.make t1 in 
        let r2, _ = R.make t2 in
        R.equal r1 r2

      (***)

      exception Unif_fails

      let mk_sy_subst uf pt_l sb_l = 
        assert (L.length pt_l = L.length sb_l);
        L.fold_left2
          (fun sT x v -> 
            if false then fprintf fmt "unif %a avec %a@." Sy.print x T.print v;
            try
              let v' = SubstT.find x sT in
              if not (x_query uf v v') then raise Unif_fails;
              sT
            with Not_found -> SubstT.add x v sT
              
          ) SubstT.empty pt_l sb_l

      let mk_ty_subst pt_l sb_l = 
        assert (L.length pt_l = L.length sb_l);
        L.fold_left2
          (fun sTy pty tty-> 
            if verbose then 
              fprintf fmt "unif %a avec %a@." Ty.print pty Ty.print tty;
            try Ty.matching sTy pty tty
            with e -> 
              if verbose then fprintf fmt "fails@.";
              raise e
          ) Ty.esubst pt_l sb_l

      let make_subst uf syl tyl pt = 
        try 
          if verbose then fprintf fmt "---pat = %a@." T.print pt;
          let varl, vtyl = typed_string_repr pt in
          mk_sy_subst uf varl syl , mk_ty_subst vtyl tyl
        with Unif_fails | Ty.TypeClash _ -> raise Unif_fails
        
      module MatchR = Set.Make
        (struct
          type t = T.t list * Ty.t list * (T.t * Tset.t)

          let compare (_,_,(s1,tset1)) (_,_,(s2,tset2)) =
            let c = T.compare s1 s2 in
            if c <> 0 then c 
            else Tset.compare tset1 tset2
         end)
      
      (* pas de filtrage modulo pour le moment *)
      let filter_good class_of tau sy =
        L.fold_left
          (fun acc t ->
            let ({T.f=f;xs=xs} as v) = T.view t in
            if Sy.equal sy f then
              let _ = 
                if verbose then
                  fprintf fmt " :::: %a = %a modulo eq@." 
                    T.print tau T.print t 
              in
              (t,v)::acc 
            else acc
          )[] (class_of tau)
        

      let ty_mapping ty l = 
        L.fold_left (fun acc (sT,sTy,pts) -> (sT, ty::sTy, pts) :: acc) [] l 

      let sy_mapping t l = 
        L.fold_left (fun acc (sT,sTy,pts) -> (t::sT, sTy, pts) :: acc) [] l

      let rec match_star class_of (t,v) l sb_dn = 
        if verbose then 
          fprintf fmt "    match star %a |-> %a@." Sy.print star T.print t;
        let tmp = T.make v.T.f [] v.T.ty in
        sy_mapping t (match_ty class_of (t, T.view tmp) l sb_dn)

      and match_ty class_of (t,v) l sb_dn = 
        if verbose then fprintf fmt "  TY of %a@." T.print t;
        let l = 
          L.fold_left 
            (fun acc t -> 
              (t, T.view t)::acc) l (L.rev v.T.xs) in
        ty_mapping v.T.ty (match_term false class_of l sb_dn)

      and match_sy not_mod_eq class_of tl sy sb_dn =
        match tl with
          | [] -> []
          | (t,v) :: l ->
            if verbose then 
              fprintf fmt "  SY %a with:\t%a@." Sy.print sy T.print t;
            if Sy.equal sy star then match_star class_of (t,v) l sb_dn
            else 
              if not_mod_eq then 
                if Sy.equal sy v.T.f then match_ty class_of (t,v) l sb_dn
                else []
              else 
                L.fold_left
                  (fun acc tv -> (match_ty class_of tv l sb_dn) @ acc)
                  [] (filter_good class_of t sy)
                  
      and match_term toplevel class_of tl = function
        | Lf (s,ps) -> 
          if verbose then fprintf fmt "Le lhs %a -> OK@." T.print s;
          [[],[],(s,ps)]
        | Nd mp ->
          Smap.fold 
            (fun sy sb_dn acc -> 
              (match_sy toplevel class_of tl sy sb_dn) @ acc) mp []
          

      let canon_term dn class_of tr =
        (* astuce pour appliquer le canonizer de la theorie. 
           Cela se fait en une seule etape dans AC(X) *)
        let tr = R.term_of (fst (R.make tr)) in
        let res = match_term true class_of [tr, T.view tr] dn in
        let st = List.fold_left (fun s e -> MatchR.add e s) MatchR.empty res in
        let res  = MatchR.elements st in

        if verbose then Debug.print_matched res;
        match res with
          | [] -> tr
          | [syl, tyl, (s,tset)] when Tset.cardinal tset = 1 -> 
            begin
              try
                let (sbT, sbsTy) as sbt = make_subst () syl tyl s in
                let t = Tset.choose tset in
                if verbose then 
                  fprintf fmt ">>subst: %a | %a @."
                    SubstT.print sbT Ty.print_subst sbsTy;
                let inst = T.apply_subst sbt t in
                if verbose then 
                  fprintf fmt "> applying this subst on %a@. yields %a@."
                    T.print t T.print inst;
                if Sy.Set.is_empty (T.vars_of inst) && 
                  Ty.Svty.is_empty (T.vty_of inst) then
                  inst
                else 
                  let _ = 
                    fprintf fmt 
                      "Bad rewrite rule: NOT(Vars(%a) in Vars(%a))@."
                      T.print s T.print t in
                  assert false
              with Unif_fails -> tr
            end 
          | [syl, tyl, (s,tset)] -> 
            if verbose then 
              begin
                fprintf fmt "Pb de Confluence I ??@.";
                fprintf fmt "--->@.%a@.<----@."
                  T.print_list (Tset.elements tset)
              end;
            assert false

          | l -> 
            if verbose then 
              begin
                fprintf fmt "Pb de Confluence II ??@.";
                List.iter
                  (fun (syl, tyl, (s,tset)) ->
                    fprintf fmt "--->@.%a@.<----@."
                      T.print_list (Tset.elements tset)
                  )l
              end;
            tr
      (* assert false*)

      let rec canon_rec dn class_of t = 
        if verbose then fprintf fmt "[URS] canon du terme %a@." T.print t;
        let {T.f=f; xs=xs; ty=ty} = T.view t in
        let xs = List.map (canon_rec dn class_of) xs in
        let t = T.make f xs ty in
        canon_term dn class_of t
               
      let canon_leaf dn class_of r =
        if verbose then fprintf fmt "@.[URS] canon de la valeur %a@." R.print r;
        let tr = R.term_of r in 
        let t = canon_rec dn class_of tr in
        fst (R.make t)
(*

        let toplevel = true in
        let tl = [ tr, T.view tr ] in 
        let res = match_term toplevel class_of tl dn in
        if verbose then Debug.print_matched res;
        match res with
          | [] -> r
          | [syl, tyl, (s,tset)] when Tset.cardinal tset = 1 -> 
            begin
              try
                let (sbT, sbsTy) as sbt = make_subst () syl tyl s in
                let t = Tset.choose tset in
                if verbose then 
                  fprintf fmt ">>subst: %a | %a @."
                    SubstT.print sbT Ty.print_subst sbsTy;
                let inst = T.apply_subst sbt t in
                if verbose then 
                  fprintf fmt "> applying this subst on %a@. yields %a@."
                    T.print t T.print inst;
                if Sy.Set.is_empty (T.vars_of inst) && 
                  Ty.Svty.is_empty (T.vty_of inst) then
                  let rinst = fst (R.make inst) in
                  if R.compare r rinst > 0 then 
                    rinst
                  else 
                    let _ = 
                      if verbose then 
                        fprintf fmt "Warning! Bad reduction: NOT(%a > %a)@."
                          R.print r R.print rinst in
                    rinst
                else 
                  let _ = 
                    fprintf fmt 
                      "Bad rewrite rule: NOT(Vars(%a) in Vars(%a))@."
                      T.print s T.print t in
                  assert false
              with Unif_fails -> r
            end 
          | [syl, tyl, (s,tset)] -> 
            if verbose then 
              begin
                fprintf fmt "Pb de Confluence I ??@.";
                fprintf fmt "--->@.%a@.<----@."
                  T.print_list (Tset.elements tset)
              end;
            assert false

          | l -> 
            if verbose then 
              begin
                fprintf fmt "Pb de Confluence II ??@.";
                List.iter
                  (fun (syl, tyl, (s,tset)) ->
                    fprintf fmt "--->@.%a@.<----@."
                      T.print_list (Tset.elements tset)
                  )l
              end;
            assert false
*)
      let canon dn class_of r =
        let sbsl = 
          List.map (fun lf -> lf, (canon_leaf dn class_of lf)) (R.leaves r) 
        in
        L.fold_left
          (fun r (p,v) ->
            if R.equal p v then r 
            else R.subst p v r
          ) r sbsl
            
  end

  (**********************************************************)

  type t = { 

    (* term -> [t] *)
    make : R.r MapT.t; 
    
    (* representative table *)
    repr : (R.r * Ex.t) MapR.t; 
    
    (* r -> class (of terms) *)
    classes : SetT.t MapR.t;
    
    (*associates each value r with the set of semantical values whose
      representatives contains r *)
    gamma : SetR.t MapR.t; 
    
    (* the disequations map *)
    neqs: Ex.t MapR.t MapR.t; 
    
    (*AC rewrite system *)
    ac_rs : SetRL.t RS.t;

    (* user rewrite system*)
    u_rs : URS.t;
  }
      
  let empty = { 
    make  = MapT.empty; 
    repr = MapR.empty;
    classes = MapR.empty; 
    gamma = MapR.empty;
    neqs = MapR.empty;
    ac_rs = RS.empty;
    u_rs = URS.empty
  }

  module Print = struct

    let rs_print fmt = SetR.iter (fprintf fmt "\t%a@." R.print)
    let rm_print fmt = 
      MapR.iter (fun k dep -> fprintf fmt "%a %a" R.print k Ex.print dep)

    let t_print fmt = SetT.iter (fprintf fmt "%a " T.print)
      
    let pmake fmt m = 
      fprintf fmt "[.] map:\n";
      MapT.iter (fun t r -> fprintf fmt "%a -> %a\n" T.print t R.print r) m
	
    let prepr fmt m = 
      fprintf fmt "------------- UF: Representatives map ----------------@.";
      MapR.iter 
	(fun r (rr,dep) -> 
	  fprintf fmt "%a --> %a %a\n" R.print r R.print rr Ex.print dep) m

    let prules fmt s = 
      fprintf fmt "------------- UF: Rewrite rules ----------------------@.";
      RS.iter
	(fun k srl -> 
	  SetRL.iter
	    (fun (ac,d)-> fprintf fmt "%a ~~> %a\n" 
              R.print (R.ac_embed ac) R.print d)srl )s
	
    let pclasses fmt m = 
      fprintf fmt "------------- UF: Class map --------------------------@.";
      MapR.iter 
	(fun k s -> fprintf fmt "%a -> %a\n" R.print k Term.print_list 
	  (SetT.elements s)) m

    let pgamma fmt m = 
      fprintf fmt "------------- UF: Gamma map --------------------------@.";
      MapR.iter (fun k s -> fprintf fmt "%a -> \n%a" R.print k rs_print s) m 
	
    let pneqs fmt m = 
      fprintf fmt "------------- UF: Disequations map--------------------@.";
      MapR.iter (fun k s -> fprintf fmt "%a -> %a\n" R.print k rm_print s) m

    let all fmt env = 
      fprintf fmt "------------------------------------------------------@.";
      fprintf fmt "%a %a %a %a %a" 
        pmake env.make 
        prepr env.repr 
        prules env.ac_rs 
        pclasses env.classes
        pneqs env.neqs;
      fprintf fmt "------------------------------------------------------@."

  end

  let mem env t = MapT.mem t env.make
    
  let lookup_by_t t env =
    try MapR.find (MapT.find t env.make) env.repr
    with Not_found -> 
      if debug_uf then fprintf fmt "Uf: Not_found %a@." Term.print t;
      assert false (*R.make t, Ex.empty*) (* XXXX *)

  let lookup_by_r r env = 
    try MapR.find r env.repr with Not_found -> r, Ex.empty

  let lookup_for_neqs env r =
    try MapR.find r env.neqs with Not_found -> MapR.empty
      
  let class_of env t = 
    try 
      let rt, _ = MapR.find (MapT.find t env.make) env.repr in
      SetT.elements (MapR.find rt env.classes)
    with Not_found -> [t]

(*
  let class_of env t = 
    let l = class_of env t in
    if rewriting then l
    else 
      List.fold_left
        (fun acc t -> (URS.canon_term env.u_rs (class_of env) t) :: acc )l l
*)
  
  module Env = struct

    let add_to_classes t r classes =  
      MapR.add r 
	(SetT.add t (try MapR.find r classes with Not_found -> SetT.empty))
	classes
	
    let update_classes c nc classes = 
      let s1 = try MapR.find c classes with Not_found -> SetT.empty in
      let s2 = try MapR.find nc classes with Not_found -> SetT.empty in
      MapR.add nc (SetT.union s1 s2) classes
	
    let add_to_gamma r c gamma = 
      L.fold_left
	(fun gamma x -> 
	  let s = try MapR.find x gamma with Not_found -> SetR.empty in
	  MapR.add x (SetR.add r s) gamma) gamma (R.leaves c)
	
    let merge r1 m1 r2 m2 dep neqs = 
      let m , neqs = 
	MapR.fold 
	  (fun k ex1 (m,neqs) -> 
	    if MapR.mem k m2 then
	      m , MapR.add k (MapR.remove r1 (MapR.find k neqs)) neqs
	    else
	      let ex = Ex.union ex1 dep in
	      let mk = MapR.add r2 ex (MapR.remove r1 (MapR.find k neqs)) in
	      MapR.add k ex m , MapR.add k mk neqs
	  )
	  m1 (m2,neqs)
      in
      MapR.add r2 m neqs

    let update_neqs r1 r2 dep env = 
      let neqs, m1 = 
	try env.neqs, MapR.find r1 env.neqs 
	with Not_found -> MapR.add r1 MapR.empty env.neqs, MapR.empty in
      let neqs, m2 = 
	try neqs, MapR.find r2 neqs 
	with Not_found -> MapR.add r2 MapR.empty neqs, MapR.empty in
      (try let exs1 =  Ex.union dep (MapR.find r2 m1) in 
           raise (Inconsistent exs1)
       with Not_found -> ());
      (try let exs2 =  Ex.union dep (MapR.find r1 m2) in 
           raise (Inconsistent exs2)
       with Not_found -> ());	
      (* if MapR.mem r2 m1 or MapR.mem r1 m2 then raise Inconsistent; *)
      merge r1 m1 r2 m2 dep neqs

    let disjoint_union l_1 l_2 = 
      let rec di_un (l1,c,l2) (l_1,l_2)= 
        match l_1,l_2 with
	  | [],[] -> l1, c, l2
	  | l, [] -> di_un (l @ l1,c,l2) ([],[])
	  | [], l -> di_un (l1,c,l @ l2) ([],[])
	  | (a,m)::r, (b,n)::s ->
	    let cmp = R.compare a b in
	    if cmp = 0 then
	      if m = n then di_un (l1,(a,m)::c,l2) (r,s)
	      else if m > n then di_un ((a,m-n)::l1,(a,n)::c,l2) (r,s)
	      else di_un (l1,(b,n)::c,(b,n-m)::l2) (r,s)
	      else if cmp > 0 then di_un ((a,m)::l1,c,l2) (r,(b,n)::s)
	      else di_un (l1,c,(b,n)::l2) ((a,m)::r,s)
      in di_un ([],[],[]) (l_1,l_2)

    exception List_minus_exn
    let list_minus l_1 l_2 = 
      let rec di_un l1 l_1 l_2 = 
        match l_1, l_2 with
	    [],[] -> l1
	  | l, [] -> l @ l1
	  | [], l -> raise List_minus_exn
	  | (a,m)::r, (b,n)::s ->
	    let cmp = R.compare a b in
	    if cmp = 0 then
	      if m = n then di_un l1 r s
	      else if m > n then di_un ((a,m-n)::l1) r s
	      else raise List_minus_exn
	      else if cmp > 0 then di_un ((a,m)::l1) r ((b,n)::s)
	      else raise List_minus_exn
      in di_un [] l_1 l_2


    exception Not_possible of Ac.t * bool
        
    let rec apply_rule (p,v) (ar,fixpoint) =
      let c = Ac.compare ar p in
      if c = 0 then {ar with l=[v,1]}, fixpoint
      else if c < 0 then raise (Not_possible (ar,fixpoint))
      else 
        try 
          let ar = {ar with l=Ac.add ar.h (v,1) (list_minus ar.l p.l)} in
          apply_rule (p,v) (ar, false)
        with List_minus_exn -> (ar,fixpoint)


    let rec apply_rs ac rls = 
      let ac2,fixpoint = 
        try SetRL.fold apply_rule rls (ac,true) 
        with Not_possible (ac2, fixpoint) -> ac2,fixpoint in
      if fixpoint then ac2 else apply_rs ac2 rls
  	

    let filter_leaves r = 
      L.fold_left 
	(fun (p,q) r -> match R.ac_extract r with 
	  | None    -> SetR.add r p, q
	  | Some ac -> p, SetAc.add ac q
	)(SetR.empty,SetAc.empty) (R.leaves r)
	
    let canon_empty st env = 	
      SetR.fold
	(fun p ((z, ex) as acc) -> 
          let q, ex_q = lookup_by_r p env in 
	  if R.equal p q then acc else (p,q)::z, Ex.union ex_q ex)
	st ([], Ex.empty)

    let canon_ac st env = 
      SetAc.fold
	(fun ac z ->
	  let rac = apply_rs ac (RS.find ac.h env.ac_rs) in
	  if Ac.compare ac rac = 0 then z
	  else (R.color ac, R.color rac) :: z )st []
	
    let canon_aux rx = L.fold_left (fun r (p,v) -> R.subst p v r) rx
      
    let rec canon env r ex_r = 
      let se, sac = filter_leaves r in
      let subst, ex_subst = canon_empty se env in
      let sac = canon_ac sac env in (* explications? *)
      let r2 = canon_aux (canon_aux r sac) subst in
      let r2 = (* explications ? *)
        if Options.rewriting then
          URS.canon env.u_rs (class_of env) r2 
        else r2
      in
      let ex_r2 = Ex.union ex_r ex_subst in
      if R.equal r r2 then r2, ex_r2 else canon env r2 ex_r2

    let canon env r =
      let rr, ex = canon env r Ex.empty in
      if rewriting && verbose then 
        fprintf fmt "canon %a = %a@." R.print r R.print rr;
      rr,ex

    let find_or_canon env r =
      try MapR.find r env.repr with Not_found -> canon env r

    (* A revoir *)
    let add_sm dep env r rr = 
      if debug_uf then 
        fprintf fmt "add_sm:  %a --> %a@." R.print r R.print rr;
      if MapR.mem r env.repr then env 
      else 
	{ env with
	  repr    = MapR.add r (rr, dep) env.repr;
	  classes = update_classes r rr env.classes;
	  gamma   = add_to_gamma r rr env.gamma ;
	  neqs    = update_neqs r rr dep env } 
          
    let init_term env t = 
      let mkr, ctx = R.make t in
      let rp, ex = canon env mkr in
      {env with
	make    = MapT.add t mkr env.make; 
	repr    = MapR.add mkr (rp,ex) env.repr;
	classes = add_to_classes t rp env.classes;
	gamma   = add_to_gamma mkr rp env.gamma;
	neqs    = 
	  if MapR.mem rp env.neqs then env.neqs 
	  else MapR.add rp MapR.empty env.neqs}, ctx


    let add_cp env (x, y, dep) = 
      let rx, ex_rx = find_or_canon env x in
      let ry, ex_ry = find_or_canon env y in
      let ex = Ex.union dep (Ex.union ex_rx ex_ry) in
      if R.equal rx ry then env
      else 
	let env = add_sm Ex.empty env rx rx in
	let env = add_sm Ex.empty env ry ry in
        if debug_ac then
          fprintf fmt "[uf] critical pair: %a = %a@." R.print rx R.print ry;
        Queue.push (rx, ry, ex) equations;
        env

    let head_cp env (({h=h} as ac), v, dep) = 
      try 
        SetRL.fold
	  (fun (p,_P) env ->
	    match disjoint_union ac.l p.l with
	      | _  , [] , _  -> env
	      | l1 , cm , l2 -> 
		let x = {ac with l = Ac.add h (_P,1) l1} in
		let y = {p  with l = Ac.add h (v,1)  l2} in
		add_cp env (R.color x, R.color y, dep)
	  )(RS.find h env.ac_rs) env
      with Not_found -> env
	
    let comp_collapse env (p, v, dep) = 
      RS.fold
	(fun h rls env ->
          SetRL.fold
	    (fun (g, d) env ->
	      let env = {env with ac_rs = RS.remove_rule (g,d) env.ac_rs} in
	      let gx = R.color g in
	      let ex_g = 
                try snd (MapR.find gx env.repr) 
	        with Not_found -> Ex.empty in
	      let ex_d = 
                try snd (MapR.find d env.repr)
	        with Not_found -> Ex.empty in
	      let g2, _ = canon env (Ac.subst p v g) in
	      let d2, _ = canon env (R.subst p v d) in
	      let ex = Ex.union (Ex.union ex_g ex_d) dep in
	      if R.equal g2 gx then 
	      (* compose *)
	        {env with ac_rs= RS.add_rule (g,d2) env.ac_rs}
	      else 
	      (* collapse *)
	        let env = add_sm Ex.empty env g2 g2 in
	        let env = add_sm Ex.empty env d2 d2 in
                if debug_ac then
                  fprintf fmt "[uf] collapse: %a = %a@." R.print g2 R.print d2;
                Queue.push (g2, d2, ex) equations;
	        env
	    ) rls env
	) env.ac_rs env
	
    let update_rs env (p, v, dep) = 
      match R.ac_extract p with
	| None -> 
	  comp_collapse env (p, v, dep)
	| Some ac -> 
	  let env = {env with ac_rs = RS.add_rule (ac,v) env.ac_rs} in
	  let env = comp_collapse env (p, v, dep) in
	  head_cp env (ac, v, dep)
	    
    let up_uf_sigma env tch (p, v, dep) =
      let use_p = 
	try 
	  MapR.find p env.gamma
	with Not_found ->
          fprintf fmt "The key %a is not found@." R.print p;
          assert false
      in
      try SetR.fold 
	    (fun r (env, touched) -> 
	      let rr,ex = lookup_by_r r env in
	      let nrr   = R.subst p v rr in
	      if R.equal rr nrr then env, touched
	      else 
	        let ex  = Ex.union ex dep in
	        let env = {
	          env with
		    repr = MapR.add r (nrr,ex) env.repr;
		    classes = update_classes rr nrr env.classes;
		    gamma = add_to_gamma r nrr env.gamma ;
		    neqs = update_neqs rr nrr dep env } in
	        env, (r,nrr,ex)::touched
	    ) use_p (env,[])
      with Not_found -> assert false
    (* il faut faire le menage dans les maps *)

    (* quelle vraie valeur pour dep ? 
       let up_uf_rs dep env =
       MapR.fold
       (fun r (rr,ex) env ->
       let nrr,_ = canon env rr in
       if R.equal nrr rr then env 
       else 
       {env with
       repr = MapR.add r (nrr,ex) env.repr;
       classes = update_classes rr nrr env.classes;
       gamma = add_to_gamma r nrr env.gamma ;
       neqs = update_neqs rr nrr dep env }
       )env.repr env
    *)
    let up_uf_rs dep env tch =
      MapR.fold
	(fun r (rr,ex) (env,tch) ->
	  let nrr,_ = canon env rr in
	  if R.equal nrr rr then env, tch
	  else 
            let env = 
	      {env with
	        repr = MapR.add r (nrr,ex) env.repr;
	        classes = update_classes rr nrr env.classes;
	        gamma = add_to_gamma r nrr env.gamma ;
	        neqs = update_neqs rr nrr dep env } in
            env, (r,[r,nrr,ex],nrr)::tch
	)env.repr (env,tch)

    let update_uf env tch (p, v, dep) =  
      let env, touched = up_uf_sigma env tch (p, v, dep) in 
      up_uf_rs dep env ((p,touched,v) :: tch)
	
  end
    
  let add env t = 
    if MapT.mem t env.make then env, [] else Env.init_term env t

  let add_semantic env r =
    if MapR.mem r env.repr then env 
    else 
      let rr, ex = Env.canon env r in
      Env.add_sm (*Ex.everything*) ex  env r rr



  let ac_solve  (env,tch) (p, v, dep) = 
    if debug_uf then 
      printf "[uf] ac-solve: %a |-> %a %a@." R.print p R.print v Ex.print dep;

    let rp, ex_rp = Env.find_or_canon env p in
    let rv, ex_rv = Env.find_or_canon env v in

    let ex = Ex.union (Ex.union ex_rp ex_rv) dep in
    
    if R.equal p rp then
      (*pour garder les représentants des valeurs ac sinon ça cause pb*)
      let env = match R.ac_extract p with
        | None    -> Env.add_sm Ex.empty env p p  (*env *)
        | Some ac -> Env.add_sm dep env p v 
      in
      let env      = Env.update_rs env (rp, rv, ex) in
      let env, tch = Env.update_uf env tch (rp, rv, ex) in
      env, tch
    else
      begin
        fprintf fmt "@.[uf] ac_solve: %a |-> %a, but we have@." 
	  R.print p R.print v;
        fprintf fmt "[uf] ac_solve: repr (%a) = %a !! bad substitution !@."
          R.print p R.print rp;
        assert false
      end
  (* XXX : pas util puisque les substs doivent être 
     triées vis à vis du membre gauche 
     let env = Env.add_sm dep env rp rp in
     let env = Env.add_sm dep env rv rv in
     env, tch, (rp,rv) :: psi
  *)

  let x_solve env r1 r2 = 
    let rr1, _ = lookup_by_r r1 env in
    let rr2, _ = lookup_by_r r2 env in
    if debug_uf then 
      printf "[uf] x-solve: %a = %a@." R.print rr1 R.print rr2;

    if R.equal rr1 rr2 then [] (* Remove rule *)
    else 
      begin
        (* if rr1 is known to be different from rr2, there is inconsistency *)
        let nq_rr1 = lookup_for_neqs env rr1 in
        let nq_rr2 = lookup_for_neqs env rr2 in
	(try let exs1 =  MapR.find rr2 nq_rr1 in raise (Inconsistent exs1)
	 with Not_found -> ());
	(try let exs2 =  MapR.find rr1 nq_rr2 in raise (Inconsistent exs2)
	 with Not_found -> ());
	(* if MapR.mem rr2 nq_rr1 then raise Inconsistent; *)
        (* if MapR.mem rr1 nq_rr2 then raise Inconsistent; *)

        (* solve the equation rr1 = rr2 *)
        let repr r = fst (lookup_by_r r env) in
        R.solve repr rr1 rr2 
      end
        
        
  let rec ac_x env tch = 
    if Queue.is_empty equations then env, tch
    else 
      let r1, r2, dep = Queue.pop equations in
      if debug_uf then 
	printf "[uf] ac(x): delta (%a) = delta (%a)@." 
	  R.print r1 R.print r2;
      let sbs = x_solve env r1 r2 in
      let sbs = List.map (fun (x, y) -> x, y, dep) sbs in
      let env, tch = L.fold_left ac_solve (env,tch) sbs in
      if debug_uf then Print.all fmt env;
      ac_x env tch
      
  let union env r1 r2 dep =
    try 
      Queue.clear equations;
      Queue.push (r1,r2, dep) equations;
      ac_x env []
    with Unsolvable -> raise (Inconsistent dep)

  let make_distinct env r1 r2 dep = 
    let d1 = lookup_for_neqs env r1 in
    let d2 = lookup_for_neqs env r2 in
    let neqs = 
      if MapR.mem r2 d1 then env.neqs else 
	MapR.add r1 (MapR.add r2 dep d1) 
	  (MapR.add r2 (MapR.add r1 dep d2) env.neqs) 
    in
    { env with neqs = neqs}

  let rec distinct_r env r1 r2 ex1 ex2 dep =
    let r1, ex1 = lookup_by_r r1 env in
    let r2, ex2 = lookup_by_r r2 env in
    let dep' = Ex.union ex1 (Ex.union ex2 dep) in
    (* r1 and r2 could not be equal *)
    if R.equal r1 r2 then raise (Inconsistent dep);
    let env = make_distinct env r1 r2 dep' in
    let repr r = fst (lookup_by_r r env) in
    (*
      match (try R.solve repr r1 r2 with Unsolvable -> []) with
      [a,b] -> make_distinct env a b dep'
      | _     -> env
    *)
    try match R.solve repr r1 r2 with
      | [a,b] -> make_distinct env a b dep'
      | []  -> raise (Inconsistent dep)
      | _   -> env
    with Unsolvable -> env


  let rec distinct env t1 t2 dep = 
    if debug_uf then 
      printf "[uf] distinct %a <> %a@." T.print t1 T.print t2;
    
    (* add is already done in Cc.assume ? 
       let env = add (add env t1) t2 in*)
    let r1, ex1 = lookup_by_t t1 env in
    let r2, ex2 = lookup_by_t t2 env in
    if debug_uf then 
      begin
	printf "[uf] delta (%a) = %a@." T.print t1 R.print r1;
	printf "[uf] delta (%a) = %a@." T.print t2 R.print r2
      end;
    distinct_r env r1 r2 ex1 ex2 dep

  let equal env t1 t2 = 
    let r1, _ = lookup_by_t t1 env in
    let r2, _ = lookup_by_t t2 env in
    R.equal r1 r2

  let are_in_neqs env r1 r2 = 
    (try MapR.mem r1 (MapR.find r2 env.neqs) with Not_found -> false) ||
      (try MapR.mem r2 (MapR.find r1 env.neqs) with Not_found -> false)

  let are_distinct env t1 t2 = 
    let b= 
      let r1,_ = lookup_by_t t1 env in
      let r2,_ = lookup_by_t t2 env in
      if R.equal r1 r2 then false
      else
	are_in_neqs env r1 r2 ||
          try 
            let repr r = fst (lookup_by_r r env) in
	    L.exists 
	      (fun (a,b) -> are_in_neqs env a b) 
	      (R.solve repr r1 r2)
          (* True because r1=r2 <-> /\_{(a,b)in(R.solve r1 r2)}  a=b *)
          with Unsolvable -> true
    (*      try
	    match T.view t1 , T.view t2 with
	    {T.f=S.Int n1} , {T.f=S.Int n2} -> HS.compare n1 n2 <> 0
	    | _ -> 
	    let nt1 = MapR.find (find m t1) m.neqs in
	    let nt2 = MapR.find (find m t2) m.neqs in
	    SetT.mem t1 nt2 || SetT.mem t2 nt1
            with Not_found -> false*)
    in     
    if debug_uf then
      printf " [uf] are_distinct %a <> %a ? %b@." 
	T.print t1 T.print t2 b; 
    b

  let explain env t1 t2 = 
    if Term.equal t1 t2 then Ex.empty
    else
      let r1, ex1 = MapR.find (MapT.find t1 env.make) env.repr in
      let r2, ex2 = MapR.find (MapT.find t2 env.make) env.repr in
      if R.equal r1 r2 then Ex.union ex1 ex2 
      else raise NotCongruent

  let neq_explain env t1 t2 = 
    let r1, ex1 = lookup_by_t t1 env in
    let r2, ex2 = lookup_by_t t2 env in
    if not (R.equal r1 r2) then Ex.union ex1 ex2 
    else raise NotCongruent
      
  let find env t = lookup_by_t t env

  let find_r env r = lookup_by_r r env

  let print = Print.all 

  let rewrite_system env rules = 
    if Options.rewriting then 
      {env with u_rs = List.fold_left URS.add env.u_rs rules}
    else env

end
