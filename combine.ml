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

  (* Xi < Term < Ac *)
  type r =
    | Term  of Term.t (* XXX changement de l'ordre pour Arrays *)
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
      
  let rec compare a b = 
    let c = compare_tag a b in 
    if c = 0 then comparei a b else c

  and compare_tag a b = 
    Pervasives.compare (theory_num a) (theory_num b)
      
  and comparei a b = 
    match a, b with
      | X1 x, X1 y -> X1.compare x y
      | X2 x, X2 y -> X2.compare x y
      | X3 x, X3 y -> X3.compare x y
      | X4 x, X4 y -> X4.compare x y
      | X5 x, X5 y -> X5.compare x y
      | Term x  , Term y  -> Term.compare x y
      | Ac x    , Ac    y -> AC.compare x y
      | _                 -> assert false

  and theory_num x = Obj.tag (Obj.repr x)

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
    if verbose then 
      match r with
        | X1 t    -> fprintf fmt "X1(%s):[%a]" X1.name X1.print t
        | X2 t    -> fprintf fmt "X2(%s):[%a]" X2.name X2.print t
        | X3 t    -> fprintf fmt "X3(%s):[%a]" X3.name X3.print t
        | X4 t    -> fprintf fmt "X3(%s):[%a]" X4.name X4.print t
        | X5 t    -> fprintf fmt "X3(%s):[%a]" X5.name X5.print t
        | Term t  -> fprintf fmt "FT:[%a]" Term.print t
        | Ac t    -> fprintf fmt "Ac:[%a]" AC.print t
          
    else 
      match r with
        | X1 t    -> fprintf fmt "%a" X1.print t
        | X2 t    -> fprintf fmt "%a" X2.print t
        | X3 t    -> fprintf fmt "%a" X3.print t
        | X4 t    -> fprintf fmt "%a" X4.print t
        | X5 t    -> fprintf fmt "%a" X5.print t
        | Term t  -> fprintf fmt "%a" Term.print t
        | Ac t    -> fprintf fmt "%a" AC.print t

            
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

  let term_extract = function Term t -> Some t | _ -> None

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
      X2.is_mine_symb sb,
      X3.is_mine_symb sb,
      X4.is_mine_symb sb,
      X5.is_mine_symb sb,
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
      X2.is_mine_symb sb,
      X3.is_mine_symb sb,
      X4.is_mine_symb sb,
      X5.is_mine_symb sb,
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
         if debug_combine then
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
    if debug_combine then
      fprintf fmt "solvej %a=%a@." print xi print xj;
    let cp , sol = partition (theory_num xj) (solvei  xi xj) in
    solve_list  (add_mr solved cp) (List.rev_map (fun (x,y) -> y,x) sol)

  and solvei  a b =
    if debug_combine then
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


  let solve  a b =
    if debug_combine then 
      fprintf fmt "[combine] solving %a = %a yields:@." print a print b;
    let sbs = solve  a b in
    if debug_combine then begin
      let c = ref 0 in
      List.iter 
        (fun (p,v) -> 
           incr c;
           fprintf fmt " %d) %a |-> %a@." !c print p print v) sbs
    end;
    sbs


  let rec type_info = function
    | X1 t   -> X1.type_info t
    | X2 t   -> X2.type_info t
    | X3 t   -> X3.type_info t
    | X4 t   -> X4.type_info t
    | X5 t   -> X5.type_info t
    | Ac x   -> AC.type_info x
    | Term t -> let {Term.ty = ty} = Term.view t in ty
	
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
	
    let empty _ = {
      r1=X1.Rel.empty (); 
      r2=X2.Rel.empty (); 
      r3=X3.Rel.empty ();
      r4=X4.Rel.empty ();
      r5=X5.Rel.empty ();
    }
	
    let assume env sa expl = 
      let env1, seq1 = X1.Rel.assume env.r1 sa expl in
      let env2, seq2 = X2.Rel.assume env.r2 sa expl in
      let env3, seq3 = X3.Rel.assume env.r3 sa expl in
      let env4, seq4 = X4.Rel.assume env.r4 sa expl in
      let env5, seq5 = X5.Rel.assume env.r5 sa expl in
      {r1=env1; r2=env2; r3=env3; r4=env4; r5=env5}, seq1@seq2@seq3@seq4@seq5

    let instantiate env are_eq are_dist class_of sa = 
      let env1, seq1 = X1.Rel.instantiate env.r1 are_eq are_dist class_of sa in
      let env2, seq2 = X2.Rel.instantiate env.r2 are_eq are_dist class_of sa in
      let env3, seq3 = X3.Rel.instantiate env.r3 are_eq are_dist class_of sa in
      let env4, seq4 = X4.Rel.instantiate env.r4 are_eq are_dist class_of sa in
      let env5, seq5 = X5.Rel.instantiate env.r5 are_eq are_dist class_of sa in 
      {r1=env1; r2=env2; r3=env3; r4=env4; r5=env5}, seq1@seq2@seq3@seq4@seq5
	
    let query a env expl = 
      match X1.Rel.query a env.r1 expl with
	| Yes _ as ans -> ans
	| No -> match X2.Rel.query a env.r2 expl with
	    | Yes _ as ans -> ans
	    | No -> match X3.Rel.query a env.r3 expl with
		| Yes _ as ans -> ans
		| No -> match X4.Rel.query a env.r4 expl with
		    | Yes _ as ans -> ans
		    | No -> X5.Rel.query a env.r5 expl
		      
    let case_split env = 
      let seq1 = X1.Rel.case_split env.r1 in
      let seq2 = X2.Rel.case_split env.r2 in
      let seq3 = X3.Rel.case_split env.r3 in
      let seq4 = X4.Rel.case_split env.r4 in
      let seq5 = X5.Rel.case_split env.r5 in
      seq1 @ seq2 @ seq3 @ seq4 @ seq5

    let add env r =
      {r1=X1.Rel.add env.r1 r;
       r2=X2.Rel.add env.r2 r;
       r3=X3.Rel.add env.r3 r;
       r4=X4.Rel.add env.r4 r;
       r5=X5.Rel.add env.r5 r;
      }
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

and X2 : Sig.THEORY with type r = CX.r and type t = CX.r Pairs.abstract =
  Pairs.Make
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

 (* Its signature is not Sig.THEORY because it doen't provide a solver *)
and AC : Ac.S with type r = CX.r = Ac.Make(CX)

and X5 : Sig.THEORY with type r = CX.r and type t = CX.r Sum.abstract =
  Sum.Make
    (struct
       include CX
       let extract = extract5
       let embed = embed5
     end)
