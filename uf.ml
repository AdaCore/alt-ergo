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
    t -> R.r -> R.r -> Explanation.t -> 
    t * (R.r * (R.r * R.r * Explanation.t) list * R.r) list

  val distinct : t -> R.r list -> Explanation.t -> t

  val are_equal : t -> Term.t -> Term.t -> bool
  val are_distinct : t -> Term.t -> Term.t -> bool

  val class_of : t -> Term.t -> Term.t list

  val explain_equal : t -> Term.t -> Term.t -> Explanation.t
  val explain_distinct : t -> Term.t list -> Explanation.t

  val print : Format.formatter -> t -> unit
 
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
    
  module Lit = Literal.Make(struct type t = R.r include R end)
  module MapL = Lit.Map  

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
    neqs: Ex.t MapL.t MapR.t; 
    
    (*AC rewrite system *)
    ac_rs : SetRL.t RS.t;
  }
      
  let empty = { 
    make  = MapT.empty; 
    repr = MapR.empty;
    classes = MapR.empty; 
    gamma = MapR.empty;
    neqs = MapR.empty;
    ac_rs = RS.empty
  }

  module Print = struct

    let rs_print fmt = SetR.iter (fprintf fmt "\t%a@." R.print)
    let lm_print fmt = 
      MapL.iter (fun k dep -> fprintf fmt "%a %a" Lit.print k Ex.print dep)

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
      fprintf fmt "------------- UF: AC rewrite rules ----------------------@.";
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
      MapR.iter (fun k s -> fprintf fmt "%a -> %a\n" R.print k lm_print s) m

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

  
  module Env = struct

    let mem env t = MapT.mem t env.make
      
    let lookup_by_t t env =
      try MapR.find (MapT.find t env.make) env.repr
      with Not_found -> 
	if debug_uf then fprintf fmt "Uf: Not_found %a@." Term.print t;
	assert false (*R.make t, Ex.empty*) (* XXXX *)
	  
    let lookup_by_r r env = 
      try MapR.find r env.repr with Not_found -> r, Ex.empty
	
    let lookup_for_neqs env r =
      try MapR.find r env.neqs with Not_found -> MapL.empty
	
    let add_to_classes t r classes =  
      MapR.add r 
	(SetT.add t (try MapR.find r classes with Not_found -> SetT.empty))
	classes
	
    let update_classes c nc classes = 
      let s1 = try MapR.find c classes with Not_found -> SetT.empty in
      let s2 = try MapR.find nc classes with Not_found -> SetT.empty in
      MapR.remove c (MapR.add nc (SetT.union s1 s2) classes)
	
    let add_to_gamma r c gamma = 
      L.fold_left
	(fun gamma x -> 
	  let s = try MapR.find x gamma with Not_found -> SetR.empty in
	  MapR.add x (SetR.add r s) gamma) gamma (R.leaves c)
	
    let update_neqs r1 r2 dep env = 
      let nq_r1 = lookup_for_neqs env r1 in
      let nq_r2 = lookup_for_neqs env r2 in
      let mapl = 
	MapL.fold
	  (fun l1 ex1 mapl ->  
	     try 
	       let ex2 = MapL.find l1 mapl in
	       let ex = Ex.union (Ex.union ex1 ex2) dep in (* VERIF *)
	       raise (Inconsistent ex)
	     with Not_found -> 
	       MapL.add l1 (Ex.union ex1 dep) mapl) 
	  nq_r1 nq_r2
      in
      MapR.add r2 mapl (MapR.add r1 mapl env.neqs)

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
        
    let apply_rs r rls = 
      let fp = ref true in
      let r = ref r in
      let rec apply_rule (p, v) =
	let c = Ac.compare !r p in
	if c = 0 then r := {!r with l=[v, 1]}
	else if c < 0 then raise Exit
	else 
          try 
            r := {!r with l = Ac.add !r.h (v, 1) (list_minus !r.l p.l)};
	    fp := false;
            apply_rule (p, v)
          with List_minus_exn -> ()
      in
      let rec fixpoint () = 
        (try SetRL.iter apply_rule rls with Exit -> ());
	if !fp then !r else (fp := true; fixpoint ())
      in fixpoint()

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
    let add_sm env r rr dep = 
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
	  else MapR.add rp MapL.empty env.neqs}, ctx


    let add_cp env (x, y, dep) = 
      let rx, ex_rx = find_or_canon env x in
      let ry, ex_ry = find_or_canon env y in
      let ex = Ex.union dep (Ex.union ex_rx ex_ry) in
      if R.equal rx ry then env
      else 
	let env = add_sm env rx rx Ex.empty in
	let env = add_sm env ry ry Ex.empty in
        if debug_ac then
          fprintf fmt "[uf] critical pair: %a = %a@." R.print rx R.print ry;
        Queue.push (rx, ry, ex) equations;
        env

    let head_cp env (({h=h} as ac), v, dep) = 
      try 
        SetRL.fold
	  (fun (g, d) env ->
	    match disjoint_union ac.l g.l with
	      | _  , [] , _  -> env
	      | l1 , cm , l2 -> 
		let x = {ac with l = Ac.add h (d,1) l1} in
		let y = {g  with l = Ac.add h (v,1) l2} in
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
	      (* TODO : ajouter les explications dans ac_rs *)
	      let ex_g = 
                try snd (MapR.find gx env.repr) 
	        with Not_found -> Ex.empty in
	      let ex_d = 
                try snd (MapR.find d env.repr)
	        with Not_found -> Ex.empty in
	      let g2, ex_g2 = canon env (Ac.subst p v g) in
	      let d2, ex_d2 = canon env (R.subst p v d) in
	      let ex = Ex.union (Ex.union ex_g ex_d) dep in
	      if R.equal g2 gx then 
		(* compose *)
	        {env with ac_rs = RS.add_rule (g,d2) env.ac_rs}
	      else 
		(* collapse *)
	        let env = add_sm env g2 g2 Ex.empty in
	        let env = add_sm env d2 d2 Ex.empty in
                if debug_ac then
                  fprintf fmt "[uf] collapse: %a = %a@." R.print g2 R.print d2;
                Queue.push (g2, d2, ex) equations;
	        env
	    ) rls env
	) env.ac_rs env
	
    (* TODO explications: ajout de dep dans ac_rs *)
    let apply_sigma_ac env ((p, v, dep) as sigma) = 
      match R.ac_extract p with
	| None -> 
	    comp_collapse env sigma
	| Some r -> 
	    let env = {env with ac_rs = RS.add_rule (r, v) env.ac_rs} in
	    let env = comp_collapse env sigma in
	    head_cp env (r, v, dep)
	    
    let apply_sigma_uf env (p, v, dep) =
      assert (MapR.mem p env.gamma);
      let use_p = MapR.find p env.gamma in
      try 
	SetR.fold 
	  (fun r (env, touched) -> 
	     let rr, ex = MapR.find r env.repr in
	     let nrr = R.subst p v rr in
	     if R.equal rr nrr then env, touched
	     else 
	       let ex  = Ex.union ex dep in
	       let env = { 
		 env with
		   repr = MapR.add r (nrr, ex) env .repr;
		   classes = update_classes rr nrr env.classes;
		   gamma = add_to_gamma r nrr env.gamma ;
		   neqs = update_neqs rr nrr dep env } 
	       in
	       env, (r, nrr, ex)::touched
	  ) use_p (env, [])
      with Not_found -> assert false

    let up_uf_rs dep env tch =
      if RS.is_empty env.ac_rs then env, tch
      else
	MapR.fold
	  (fun r (rr,ex) (env,tch) ->
	     let nrr, ex_nrr = canon env rr in
	     if R.equal nrr rr then env, tch
	     else 
	       let ex = Ex.union ex ex_nrr in
               let env = 
		 {env with
	            repr = MapR.add r (nrr, ex) env.repr;
	            classes = update_classes rr nrr env.classes;
	            gamma = add_to_gamma r nrr env.gamma ;
	            neqs = update_neqs rr nrr dep env } in
               env, (r,[r, nrr, ex],nrr)::tch
	  ) env.repr (env, tch)
	  
    let apply_sigma env tch ((p, v, dep) as sigma) = 
      let env = add_sm env p p Ex.empty in
      let env = apply_sigma_ac env sigma in
      let env, touched = apply_sigma_uf env sigma in 
      up_uf_rs dep env ((p, touched, v) :: tch)
	
  end
    
  let add env t = 
    if MapT.mem t env.make then env, [] else Env.init_term env t

  let add_semantic env r =
    if MapR.mem r env.repr then env 
    else 
      let rr, ex = Env.canon env r in
      Env.add_sm (*Ex.everything*) env r rr ex

  let ac_solve dep (env, tch) (p, v) = 
    if debug_uf then 
      printf "[uf] ac-solve: %a |-> %a %a@." R.print p R.print v Ex.print dep;
    assert ( let rp, _ = Env.find_or_canon env p in R.equal p rp);
    let rv, ex_rv = Env.find_or_canon env v in
    let dep = Ex.union ex_rv dep in
    Env.apply_sigma env tch (p, rv, dep)

  let x_solve env r1 r2 dep = 
    let rr1, ex_r1 = Env.find_or_canon env r1 in
    let rr2, ex_r2 = Env.find_or_canon env r2 in
    let dep = Ex.union dep (Ex.union ex_r1 ex_r2) in
    if debug_uf then 
      printf "[uf] x-solve: %a = %a@." R.print rr1 R.print rr2;
    if R.equal rr1 rr2 then [] (* Remove rule *)
    else 
      begin
	ignore (Env.update_neqs rr1 rr2 dep env);
        R.solve rr1 rr2 
      end
        
  let rec ac_x env tch = 
    if Queue.is_empty equations then env, tch
    else 
      let r1, r2, dep = Queue.pop equations in
      if debug_uf then 
	printf "[uf] ac(x): delta (%a) = delta (%a)@." 
	  R.print r1 R.print r2;
      let sbs = x_solve env r1 r2 dep in
      let env, tch = List.fold_left (ac_solve dep) (env, tch) sbs in
      if debug_uf then Print.all fmt env;
      ac_x env tch
      
  let union env r1 r2 dep =
    try
      Queue.clear equations;
      Queue.push (r1,r2, dep) equations;
      ac_x env []
    with Unsolvable -> raise (Inconsistent dep)

  let rec distinct env rl dep =
    let d = Lit.make (Literal.Distinct rl) in
    if debug_uf then fprintf fmt "[uf] distinct %a@." Lit.print d;
    let neqs, _, newds = 
      List.fold_left
	(fun (neqs, mapr, newds) r -> 
	   let rr, ex = Env.find_or_canon env r in 
	   try 
	     raise (Inconsistent (Ex.union ex (MapR.find rr mapr)))
	   with Not_found ->
	     let uex = Ex.union ex dep in
	     let mdis = 
	       try MapR.find rr neqs with Not_found -> MapL.empty in
	     let mdis = 
	       try 
		 MapL.add d (Ex.merge uex (MapL.find d mdis)) mdis
	       with Not_found -> 
		 MapL.add d uex mdis
	     in
	     MapR.add rr mdis neqs, MapR.add rr uex mapr, (rr, ex, mapr)::newds
	)
	(env.neqs, MapR.empty, [])
	rl
    in
    let env = { env with neqs = neqs } in
    List.fold_left 
      (fun env (r1, ex1, mapr) -> 
	 MapR.fold (fun r2 ex2 env -> 
		      let ex = Ex.union ex1 (Ex.union ex2 dep) in
		      try match R.solve r1 r2 with
			| [a, b] -> 
			    if (R.equal a r1 && R.equal b r2) ||
			      (R.equal a r2 && R.equal b r1) then env
			    else
			      distinct env [a; b] ex
			| []  -> raise (Inconsistent ex) 
			| _   -> env
		      with Unsolvable -> env) mapr env)
      env newds
			  
  let are_equal env t1 t2 = 
    let r1, _ = Env.lookup_by_t t1 env in
    let r2, _ = Env.lookup_by_t t2 env in
    R.equal r1 r2

  let are_in_neqs env (r1, r2) =
    try ignore (Env.update_neqs r1 r2 Ex.empty env); false
    with Inconsistent _ -> true

  let are_distinct env t1 t2 = 
    let res = 
      let r1, _ = Env.lookup_by_t t1 env in
      let r2, _ = Env.lookup_by_t t2 env in
      not (R.equal r1 r2) && 
	( are_in_neqs env (r1, r2) ||
	    try
	      List.exists (are_in_neqs env) (R.solve r1 r2)
	    with Unsolvable -> true )
    in     
    if debug_uf then
      printf " [uf] are_distinct %a <> %a ? %b@." T.print t1 T.print t2 res; 
    res

  let explain_equal env t1 t2 = 
    if Term.equal t1 t2 then Ex.empty
    else
      let r1, ex1 = Env.lookup_by_t t1 env in
      let r2, ex2 = Env.lookup_by_t t2 env in
      if not (R.equal r1 r2) then raise NotCongruent;
      Ex.union ex1 ex2 

  let explain_distinct env lt = assert false

  let class_of env t = 
    try 
      let rt, _ = MapR.find (MapT.find t env.make) env.repr in
      SetT.elements (MapR.find rt env.classes)
    with Not_found -> [t]
      
  let find env t = Env.lookup_by_t t env

  let find_r = Env.find_or_canon

  let print = Print.all 

  let mem = Env.mem

end
