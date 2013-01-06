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

let new_solvers_combination_method = true

open Format
open Options
open Sig

module rec CX : sig
  include Sig.X

  val extract1 : r -> X1.t option
  val embed1 : X1.t -> r

  val extract2 : r -> X2.t option
  val embed2 : X2.t -> r

  val extract3 : r -> X3.t option
  val embed3 : X3.t -> r

  val extract4 : r -> X4.t option
  val embed4 : X4.t -> r

  val extract5 : r -> X5.t option
  val embed5 : X5.t -> r

end =
struct

  type r =
    | Term  of Term.t
    | Ac    of AC.t
    | X1    of X1.t 
    | X2    of X2.t 
    | X3    of X3.t 
    | X4    of X4.t 
    | X5    of X5.t 
    
  let extract1 = function X1 r   -> Some r | _ -> None
  let extract2 = function X2 r   -> Some r | _ -> None
  let extract3 = function X3 r   -> Some r | _ -> None
  let extract4 = function X4 r   -> Some r | _ -> None
  let extract5 = function X5 r   -> Some r | _ -> None
  
  let embed1 x = X1 x
  let embed2 x = X2 x
  let embed3 x = X3 x
  let embed4 x = X4 x  
  let embed5 x = X5 x
	
  let is_an_eq a = 
    match Literal.LT.view a with Literal.Builtin _ -> false | _ -> true

  let is_int v = 
    let ty  = match v with
      | X1 x -> X1.type_info x
      | X2 x -> X2.type_info x
      | X3 x -> X3.type_info x
      | X4 x -> X4.type_info x
      | X5 x -> X5.type_info x
      | Term t -> (Term.view t).Term.ty
      | Ac x -> AC.type_info x
    in 
    ty = Ty.Tint
      
  let type_info = function
    | X1 t   -> X1.type_info t
    | X2 t   -> X2.type_info t
    | X3 t   -> X3.type_info t
    | X4 t   -> X4.type_info t
    | X5 t   -> X5.type_info t
    | Ac x   -> AC.type_info x
    | Term t -> let {Term.ty = ty} = Term.view t in ty

  (* Xi < Term < Ac *)
  let theory_num x = match x with  
    | Ac _    -> -1
    | Term  _ -> -2
    | X1 _    -> -3
    | X2 _    -> -4
    | X3 _    -> -5
    | X4 _    -> -6
    | X5 _    -> -7
          
  let compare_tag a b = theory_num a - theory_num b

  (*let compare a b = 
    let c = Ty.compare (type_info a) (type_info b) in
    if c <> 0 then c
    else match a, b with
      | Term x  , Term y  -> Term.compare x y
      | Ac x    , Ac    y -> AC.compare x y
      | Ac _    , Term _  -> 1
      | Term _  , Ac _    -> -1
      | X1 _, (Term _ | Ac _ | X1 _) | (Term _ | Ac _ ), X1 _ -> X1.compare a b
      | X2 _, (Term _ | Ac _ | X2 _) | (Term _ | Ac _ ), X2 _ -> X2.compare a b
      | X3 _, (Term _ | Ac _ | X3 _) | (Term _ | Ac _ ), X3 _ -> X3.compare a b
      | X4 _, (Term _ | Ac _ | X4 _) | (Term _ | Ac _ ), X4 _ -> X4.compare a b
      | X5 _, (Term _ | Ac _ | X5 _) | (Term _ | Ac _ ), X5 _ -> X5.compare a b
      | _                 -> compare_tag a b
  *)      
    
  (* ancienne version *)

  let compare a b = 
    match a, b with
      | X1 x, X1 y -> X1.compare a b
      | X2 x, X2 y -> X2.compare a b
      | X3 x, X3 y -> X3.compare a b
      | X4 x, X4 y -> X4.compare a b
      | X5 x, X5 y -> X5.compare a b
      | Term x  , Term y  -> Term.compare x y
      | Ac x    , Ac    y -> AC.compare x y
      | _                 -> compare_tag a b
    
  let equal a b = compare a b = 0

  let hash = function
    | Term  t -> Term.hash t 
    | Ac x -> AC.hash x
    | X1 x -> X1.hash x
    | X2 x -> X2.hash x
    | X3 x -> X3.hash x
    | X4 x -> X4.hash x
    | X5 x -> X5.hash x

  module MR = Map.Make(struct type t = r let compare = compare end)
    
  let print fmt r = 
    if term_like_pp () then 
      match r with
        | X1 t    -> fprintf fmt "%a" X1.print t
        | X2 t    -> fprintf fmt "%a" X2.print t
        | X3 t    -> fprintf fmt "%a" X3.print t
        | X4 t    -> fprintf fmt "%a" X4.print t
        | X5 t    -> fprintf fmt "%a" X5.print t
        | Term t  -> fprintf fmt "%a" Term.print t
        | Ac t    -> fprintf fmt "%a" AC.print t
    else 
      match r with
        | X1 t    -> fprintf fmt "X1(%s):[%a]" X1.name X1.print t
        | X2 t    -> fprintf fmt "X2(%s):[%a]" X2.name X2.print t
        | X3 t    -> fprintf fmt "X3(%s):[%a]" X3.name X3.print t
        | X4 t    -> fprintf fmt "X3(%s):[%a]" X4.name X4.print t
        | X5 t    -> fprintf fmt "X3(%s):[%a]" X5.name X5.print t
        | Term t  -> fprintf fmt "FT:[%a]" Term.print t
        | Ac t    -> fprintf fmt "Ac:[%a]" AC.print t

            
  let leaves r = 
    match r with 
      | X1 t -> X1.leaves t 
      | X2 t -> X2.leaves t 
      | X3 t -> X3.leaves t 
      | X4 t -> X4.leaves t 
      | X5 t -> X5.leaves t 
      | Ac t -> r :: (AC.leaves t)
      | Term _ -> [r]

  let ac_extract = function
      Ac t   -> Some t
    | _ -> None

  let ac_embed ({Sig.l = l} as t) = 
    match l with
      | []    -> 
	  assert false
      | [x, 1] -> x
      | l     -> 
	  let sort = List.fast_sort (fun (x,n) (y,m) -> compare x y) in
	  Ac { t with Sig.l = List.rev (sort l) }

  let term_embed t = Term t

  let term_extract r = 
    match r with 
      | X1 _ -> X1.term_extract r 
      | X2 _ -> X2.term_extract r 
      | X3 _ -> X3.term_extract r 
      | X4 _ -> X4.term_extract r 
      | X5 _ -> X5.term_extract r 
      | Ac _ -> None (* SYLVAIN : TODO *)
      | Term t -> Some t

  let subst p v r = 
    if equal p v then r 
    else match r with
      | X1 t   -> X1.subst p v t
      | X2 t   -> X2.subst p v t
      | X3 t   -> X3.subst p v t
      | X4 t   -> X4.subst p v t
      | X5 t   -> X5.subst p v t
      | Ac t   -> if equal p r then v else AC.subst p v t
      | Term _ -> if equal p r then v else r

  let make t = 
    let {Term.f=sb} = Term.view t in
    match 
      X1.is_mine_symb sb,
      not (restricted ()) && X2.is_mine_symb sb,
      not (restricted ()) && X3.is_mine_symb sb,
      not (restricted ()) && X4.is_mine_symb sb,
      not (restricted ()) && X5.is_mine_symb sb,
      AC.is_mine_symb sb 
    with
      | true  , false , false, false, false, false -> X1.make t
      | false , true  , false, false, false, false -> X2.make t
      | false , false , true , false, false, false -> X3.make t
      | false , false , false, true , false, false -> X4.make t
      | false , false , false, false, true , false -> X5.make t
      | false , false , false, false, false, true  -> AC.make t
      | false , false , false, false, false, false -> Term t, []
      | _ -> assert false
	  
  let fully_interpreted sb =
    match 
      X1.is_mine_symb sb,
      not (restricted ()) && X2.is_mine_symb sb,
      not (restricted ()) && X3.is_mine_symb sb,
      not (restricted ()) && X4.is_mine_symb sb,
      not (restricted ()) && X5.is_mine_symb sb,
      AC.is_mine_symb sb 
    with
      | true  , false , false, false, false, false -> X1.fully_interpreted sb
      | false , true  , false, false, false, false -> X2.fully_interpreted sb
      | false , false , true , false, false, false -> X3.fully_interpreted sb
      | false , false , false, true , false, false -> X4.fully_interpreted sb
      | false , false , false, false, true , false -> X5.fully_interpreted sb
      | false , false , false, false, false, true  -> AC.fully_interpreted sb
      | false , false , false, false, false, false -> false
      | _ -> assert false


  let color ac = 
    match ac.Sig.l with
      | [] -> assert false
      | [r,1] -> r
      | _ -> 
        match 
          X1.is_mine_symb ac.Sig.h, 
          X2.is_mine_symb ac.Sig.h, 
          X3.is_mine_symb ac.Sig.h, 
          X4.is_mine_symb ac.Sig.h, 
          X5.is_mine_symb ac.Sig.h, 
          AC.is_mine_symb ac.Sig.h with 
	    | true  , false , false, false, false, false -> X1.color ac
	    | false , true  , false, false, false, false -> X2.color ac
	    | false , false , true , false, false, false -> X3.color ac
	    | false , false , false, true , false, false -> X4.color ac
	    | false , false , false, false, true, false -> X5.color ac
	    | false , false , false, false, false, true  -> ac_embed ac
	    | _ -> assert false
              

  let add_mr =
    List.fold_left 
      (fun solved (p,v) -> 
	 MR.add p (v::(try MR.find p solved with Not_found -> [])) solved)

  let unsolvable = function
    | X1 x -> X1.unsolvable x
    | X2 x -> X2.unsolvable x 
    | X3 x -> X3.unsolvable x 
    | X4 x -> X4.unsolvable x 
    | X5 x -> X5.unsolvable x 
    | Ac _ | Term _  -> true
	
  let partition tag = 
    List.partition 
      (fun (u,t) -> 
	 (theory_num u = tag || unsolvable u) && 
	   (theory_num t = tag || unsolvable t))

  let rec solve_list  solved l =
    List.fold_left
      (fun solved (a,b) -> 
         if debug_combine () then
           fprintf fmt "solve_list %a=%a@." print a print b;
	 let cmp = compare a b in
	 if cmp = 0 then solved else
	   match a , b with
	       (* both sides are empty *)
	     | (Term _ | Ac _) , (Term _ | Ac _) -> 
		 add_mr solved (unsolvable_values cmp  a b)
		   
	     (* only one side is empty *)
	     | (a, b) 
                 when unsolvable a || unsolvable b ||  compare_tag a b = 0 ->
		 let a,b = if unsolvable a then b,a else a,b in
		 let cp , sol = partition (theory_num a) (solvei  b a) in
		 solve_list  (add_mr solved cp) sol
		   
	     (* both sides are not empty *)
	     | a , b -> solve_theoryj  solved a b
      ) solved l

  and unsolvable_values cmp a b =
    match a, b with
      (* Clash entre theories: On peut avoir ces pbs ? *)
      | X1 _, (X2 _ | X3 _ | X4 _ | X5 _) 
      | (X2 _ | X3 _ | X4 _ | X5 _), X1 _ 
      | X2 _, (X3 _ | X4 _ | X5 _) 
      | (X3 _ | X4 _ | X5 _), X2 _ 
      | X3 _, (X4 _ | X5 _)
      | (X4 _ | X5 _) , X3 _
      | X5 _, X4 _ -> assert false

      (* theorie d'un cote, vide de l'autre *)
      | X1 _, _ | _, X1 _ -> X1.solve a b
      | X2 _, _ | _, X2 _ -> X2.solve a b
      | X3 _, _ | _, X3 _ -> X3.solve a b
      | X4 _, _ | _, X4 _ -> X4.solve a b
      | X5 _, _ | _, X5 _ -> X5.solve a b
      | (Ac _|Term _), (Ac _|Term _) -> [if cmp > 0 then a,b else b,a]

  and solve_theoryj solved xi xj =
    if debug_combine () then
      fprintf fmt "solvej %a=%a@." print xi print xj;
    let cp , sol = partition (theory_num xj) (solvei  xi xj) in
    solve_list  (add_mr solved cp) (List.rev_map (fun (x,y) -> y,x) sol)

  and solvei  a b =
    if debug_combine () then
      fprintf fmt "solvei %a=%a@." print a print b;
    match b with
      | X1 _ -> X1.solve  a b
      | X2 _ -> X2.solve  a b
      | X3 _ -> X3.solve  a b
      | X4 _ -> X4.solve  a b
      | X5 _ -> X5.solve  a b
      | Term _ | Ac _ -> 
          (* XXX pour Arrays *)
          match a with
            | X4 _  -> X4.solve  a b
            | _ -> 
	        fprintf fmt "solvei %a = %a @." print a print b;
	        assert false

  let rec solve_rec  mt ab = 
    let mr = solve_list  mt ab in
    let mr , ab = 
      MR.fold 
	(fun p lr ((mt,ab) as acc) -> match lr with
	     [] -> assert false
	   | [_] -> acc
	   | x::lx -> 
	       MR.add p [x] mr , List.rev_map (fun y-> (x,y)) lx)	 
	mr (mr,[])
    in 
    if ab=[] then mr else solve_rec  mr ab
      
  let solve  a b =
    MR.fold 
      (fun p lr ret -> 
	 match lr with [r] -> (p ,r)::ret | _ -> assert false) 
      (solve_rec  MR.empty [a,b]) []


  let abstract_selectors a acc = 
    if false then fprintf fmt "abstract selectors of %a@." CX.print a;
    match a with
      | X1 a   -> X1.abstract_selectors a acc
      | X2 a   -> X2.abstract_selectors a acc
      | X3 a   -> X3.abstract_selectors a acc
      | X4 a   -> X4.abstract_selectors a acc
      | X5 a   -> X5.abstract_selectors a acc
      | Term _ -> a, acc
      | Ac a   -> AC.abstract_selectors a acc


  module SX = Set.Make(struct type t = r let compare = CX.compare end)

  let print_sbt msg sbs =
    if debug_combine () then begin
      let c = ref 0 in
      fprintf fmt "%s subst:@." msg;
      List.iter 
        (fun (p,v) -> 
          incr c;
          fprintf fmt " %d) %a |-> %a@." !c print p print v) sbs;
      fprintf fmt "@."
    end
    
  let apply_subst r l =
    List.fold_left (fun r (p,v) -> CX.subst p v r) r l
      
  let triangular_down sbs = 
    List.fold_right
      (fun (p,v) nsbs -> (p, apply_subst v nsbs) :: nsbs) sbs []

  let make_idemp a b sbs = 
    print_sbt "Non triangular" sbs;
    let sbs = triangular_down sbs in
    let sbs = triangular_down (List.rev sbs) in (* triangular up *)
    let original = List.fold_right SX.add (CX.leaves a) SX.empty in
    let original = List.fold_right SX.add (CX.leaves b) original in
    let sbs = 
      List.filter (fun (p,v) -> 
        match p with
          | Ac _ -> true | Term _ -> SX.mem p original
          | _ -> assert false
      )sbs 
    in
    print_sbt "Triangular and cleaned" sbs;
    assert (!Preoptions.no_asserts || 
               equal (apply_subst a sbs) (apply_subst b sbs));
    sbs

  module New_Solve = struct

    let debug_abst_result oa ob a b acc =
      fprintf fmt "@.###debug_abst_result ######################################@.";
      fprintf fmt "@.Initial equaliy:   %a = %a@." CX.print oa CX.print ob;
      fprintf fmt "abstracted equality: %a = %a@." CX.print a CX.print b;
      fprintf fmt "selectors elimination result:@.";
      let cpt = ref 0 in
      List.iter
        (fun (p,v) ->
          incr cpt;
          fprintf fmt "\t(%d) %a |-> %a@." !cpt CX.print p CX.print v
        )acc;
      fprintf fmt "@."

    let debug_abst_result_normalise oa ob a b acc =
      fprintf fmt "@.###debug_abst_result_normalise ####################@.";
      fprintf fmt "@.Initial equaliy:   %a = %a@." CX.print oa CX.print ob;
      fprintf fmt "abstracted equality: %a = %a@." CX.print a CX.print b;
      fprintf fmt "selectors elimination result:@.";
      let cpt = ref 0 in
      List.iter
        (fun (p,v) ->
          incr cpt;
          fprintf fmt "\t(%d) %a |-> %a@." !cpt CX.print p CX.print v
        )acc;
      fprintf fmt "@."

    let apply_subst_right r sbt =
      List.fold_left (fun r (p,v) -> CX.subst p v r) r sbt
    
    let apply_subst_right r sbt =
      List.fold_right (fun (p,v)r  -> CX.subst p v r) sbt r


    let assert_mem_types tya tyb =
      assert (
        (*!Preoptions.no_asserts ||*)
          if not (Ty.compare tya tyb = 0) then (
            fprintf fmt "@.Tya = %a  and @.Tyb = %a@.@." Ty.print tya Ty.print tyb;
            false)
          else true)

    let merge_sbt sbt1 sbt2 = sbt1 @ sbt2
        
    let solve_uninterpreted r1 r2 pb = 
      if CX.compare r1 r2 > 0 then { pb with sbt = (r1,r2)::pb.sbt }
      else { pb with sbt = (r2,r1)::pb.sbt }
        
    let rec new_solve_list pb =
      match pb.eqs with
        | [] -> 
          if false then print_sbt "Should be triangular and cleaned" pb.sbt;
          pb.sbt
        | (a,b) :: eqs ->
          let pb = {pb with eqs=eqs} in
          if false then 
            fprintf fmt "solve one %a = %a@." CX.print a CX.print b;
          let ra = apply_subst_right a pb.sbt in
          let rb = apply_subst_right b pb.sbt in
          if CX.equal ra rb then new_solve_list pb
          else
            let tya = CX.type_info ra in
            let tyb = CX.type_info rb in
            assert_mem_types tya tyb;
            let pb = match tya with
              | Ty.Tint 
              | Ty.Treal     -> X1.new_solve ra rb pb
              | Ty.Trecord _ -> X2.new_solve ra rb pb
              | Ty.Tbitv _   -> X3.new_solve ra rb pb
              | Ty.Tsum _    -> X5.new_solve ra rb pb
              | Ty.Tbool 
              | Ty.Text _ 
              | Ty.Tfarray _ -> solve_uninterpreted ra rb pb
              | Ty.Tnext _   -> assert false
              | Ty.Tunit     -> assert false
              | Ty.Tvar _    -> assert false
            in
            new_solve_list pb

    let new_solve oa ob a b sbt =
      if false then debug_abst_result oa ob a b sbt;
      let sbt = new_solve_list { sbt=sbt ; eqs=[a,b] } in
      make_idemp oa ob sbt


  end
    
  let solve  a b =
    if false then
      fprintf fmt "@.##################################################@.";
    if debug_combine () then 
      fprintf fmt "@.[combine] I solve %a = %a:@." print a print b;
    if new_solvers_combination_method then 
      let a', acc = abstract_selectors a [] in
      let b', acc = abstract_selectors b acc in
      New_Solve.new_solve a b a' b' acc
    else make_idemp a b (solve a b)

  module Rel =
  struct
    type elt = r
    type r = elt

    type t = { 
      r1: X1.Rel.t; 
      r2: X2.Rel.t; 
      r3: X3.Rel.t;  
      r4: X4.Rel.t; 
      r5: X5.Rel.t; 
    }
	
    let empty classes = {
      r1=X1.Rel.empty classes; 
      r2=X2.Rel.empty classes; 
      r3=X3.Rel.empty classes;
      r4=X4.Rel.empty classes;
      r5=X5.Rel.empty classes;
    }
	
    let assume env sa ~are_eq ~are_neq ~class_of ~classes =
      !Options.thread_yield ();
      let env1, { assume = a1; remove = rm1} = 
	X1.Rel.assume env.r1 sa ~are_eq ~are_neq ~class_of ~classes in
      let env2, { assume = a2; remove = rm2} = 
	X2.Rel.assume env.r2 sa ~are_eq ~are_neq ~class_of ~classes in
      let env3, { assume = a3; remove = rm3} = 
	X3.Rel.assume env.r3 sa ~are_eq ~are_neq ~class_of ~classes in
      let env4, { assume = a4; remove = rm4} = 
	X4.Rel.assume env.r4 sa ~are_eq ~are_neq ~class_of ~classes in
      let env5, { assume = a5; remove = rm5} = 
	X5.Rel.assume env.r5 sa ~are_eq ~are_neq ~class_of ~classes in
      {r1=env1; r2=env2; r3=env3; r4=env4; r5=env5}, 
      { assume = a1@a2@a3@a4@a5;
	remove = rm1@rm2@rm3@rm4@rm5;}
	
    let query env a ~are_eq ~are_neq ~class_of ~classes = 
      !Options.thread_yield ();
      match X1.Rel.query env.r1 a ~are_eq ~are_neq ~class_of ~classes with
	| Yes _ as ans -> ans
	| No -> 
	  match X2.Rel.query env.r2 a ~are_eq ~are_neq ~class_of ~classes with
	    | Yes _ as ans -> ans
	    | No ->
	      match X3.Rel.query env.r3 a ~are_eq ~are_neq ~class_of ~classes with
		| Yes _ as ans -> ans
		| No -> 
		    match X4.Rel.query env.r4 a ~are_eq ~are_neq ~class_of ~classes with
		      | Yes _ as ans -> ans
		      | No -> X5.Rel.query env.r5 a ~are_eq ~are_neq ~class_of ~classes
		      
    let case_split env = 
      !Options.thread_yield ();
      let seq1 = X1.Rel.case_split env.r1 in
      let seq2 = X2.Rel.case_split env.r2 in
      let seq3 = X3.Rel.case_split env.r3 in
      let seq4 = X4.Rel.case_split env.r4 in
      let seq5 = X5.Rel.case_split env.r5 in
      seq1 @ seq2 @ seq3 @ seq4 @ seq5

    let add env r =
      !Options.thread_yield ();
      {r1=X1.Rel.add env.r1 r;
       r2=X2.Rel.add env.r2 r;
       r3=X3.Rel.add env.r3 r;
       r4=X4.Rel.add env.r4 r;
       r5=X5.Rel.add env.r5 r;
      }

    let print_model fmt env rs =
      X1.Rel.print_model fmt env.r1 rs;
      X2.Rel.print_model fmt env.r2 rs;
      X3.Rel.print_model fmt env.r3 rs;
      X4.Rel.print_model fmt env.r4 rs;
      X5.Rel.print_model fmt env.r5 rs


    let new_terms env = 
      let t1 = X1.Rel.new_terms env.r1 in
      let t2 = X2.Rel.new_terms env.r2 in
      let t3 = X3.Rel.new_terms env.r3 in
      let t4 = X4.Rel.new_terms env.r4 in
      let t5 = X5.Rel.new_terms env.r5 in
      Term.Set.union t1
        (Term.Set.union t2
           (Term.Set.union t3 
              (Term.Set.union t4 t5)))

  end

end

and TX1 : Polynome.T with type r = CX.r = Arith.Type(CX)

and X1 : Sig.THEORY  with type t = TX1.t and type r = CX.r =
  Arith.Make(CX)(TX1)
    (struct
       type t = TX1.t
       type r = CX.r
       let extract = CX.extract1
       let embed =  CX.embed1
     end)

and X2 : Sig.THEORY with type r = CX.r and type t = CX.r Records.abstract =
  Records.Make
    (struct
       include CX
       let extract = extract2
       let embed = embed2
     end)

and X3 : Sig.THEORY with type r = CX.r and type t = CX.r Bitv.abstract =
  Bitv.Make
    (struct
       include CX
       let extract = extract3
       let embed = embed3
     end)

and X4 : Sig.THEORY with type r = CX.r and type t = CX.r Arrays.abstract =
  Arrays.Make
    (struct
       include CX
       let extract = extract4
       let embed = embed4
     end)

 (* Its signature is not Sig.THEORY because it does not provide a solver *)
and AC : Ac.S with type r = CX.r = Ac.Make(CX)

and X5 : Sig.THEORY with type r = CX.r and type t = CX.r Sum.abstract =
  Sum.Make
    (struct
       include CX
       let extract = extract5
       let embed = embed5
     end)
