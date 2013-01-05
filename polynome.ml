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
open Num
open Options

exception Not_a_num
exception Maybe_zero

module type S = sig
  type r
  val compare : r -> r -> int
  val term_embed : Term.t -> r
  val mult : r -> r -> r
  val print : Format.formatter -> r -> unit
end

module type T = sig

  type r
  type t

  val compare : t -> t -> int
  val hash : t -> int
  val create : (num * r) list -> num -> Ty.t-> t
  val add : t -> t -> t
  val sub : t -> t -> t
  val mult : t -> t -> t
  val mult_const : num -> t -> t
  val div : t -> t -> t * bool
  val modulo : t -> t -> t

  val is_num : t -> num option
  val is_empty : t -> bool
  val find : r -> t -> num
  val choose : t -> num * r
  val subst : r -> t -> t -> t
  val remove : r -> t -> t
  val to_list : t -> (num * r) list * num
    
  val print : Format.formatter -> t -> unit
  val type_info : t -> Ty.t
  val is_monomial : t -> (num * r * num) option

  val ppmc_denominators : t -> num
  val pgcd_numerators : t -> num
  val normal_form : t -> t * num * num
  val normal_form_pos : t -> t * num * num
end

module Make (X : S) = struct

  type r = X.r
      
  module M : Map.S with type key = r = 
    Map.Make(
      struct 
        type t = r 
            
        (*sorted in decreasing order to comply with AC(X) order requirements*)
        let compare x y = X.compare y x
      end)
      
  type t = { m : num M.t; c : num; ty : Ty.t }


  let num_0 = Int 0
  let num_1 = Int 1
  let num_minus_1 = Int (-1)

  let map_to_list m = List.rev (M.fold (fun x a aliens -> (a, x)::aliens) m [])

  exception Out of int

  let compare_maps l1 l2 = 
    try
      List.iter2
        (fun (a,x) (b,y) ->
           let c = X.compare x y   in if c <> 0 then raise (Out c);
           let c = compare_num a b in if c <> 0 then raise (Out c) )l1 l2;
      0
    with
      | Out c -> c 
      | Invalid_argument("List.iter2") -> List.length l1 - List.length l2
            
  let compare p1 p2 = 
    let c = Ty.compare p1.ty p2.ty in
    if c <> 0 then c
    else match M.is_empty p1.m, M.is_empty p2.m with
      | true , false -> -1
      | false, true  -> 1
      | true , true  -> compare_num p1.c p2.c
      | false, false ->
          let c =  compare_maps (map_to_list p1.m) (map_to_list p2.m) in
          if c = 0 then compare_num p1.c p2.c else c


  let hash p = 
    abs (Hashtbl.hash p.m + 19*Hashtbl.hash p.c + 17 * Ty.hash p.ty)
 
  let pprint fmt p =
    let zero = ref true in
    M.iter
      (fun x n ->
         let s, n, op = match n with
           | Int 1  -> (if !zero then "" else "+"), "", ""
           | Int -1 -> "-", "", ""
           | n ->   
               if n >/ num_0 then 
		 (if !zero then "" else "+"), string_of_num n, "*" 
               else "-", string_of_num (minus_num n), "*" 
         in
	 zero := false;
         fprintf fmt "%s%s%s%a" s n op X.print x
      ) p.m;
    let s, n = 
      if p.c >/ num_0 then (if !zero then "" else "+"), string_of_num p.c 
      else if p.c </ num_0 then "-", string_of_num (minus_num p.c)
      else (if !zero then "","0" else "","") in
    fprintf fmt "%s%s" s n


  let print fmt p =
    if Options.term_like_pp () then pprint fmt p 
    else begin
      M.iter 
        (fun t n -> fprintf fmt "%s*%a " (string_of_num n) X.print t) p.m;
      fprintf fmt "%s" (string_of_num p.c);
      fprintf fmt " [%a]" Ty.print p.ty
    end



  let is_num p = if M.is_empty p.m then Some p.c else None

  let find x m = try M.find x m with Not_found -> num_0

  let create l c ty = 
    let m = 
      List.fold_left 
	(fun m (n, x) -> 
	   let n' = n +/ (find x m) in
	   if n' =/ (num_0) then M.remove x m else M.add x n' m) M.empty l
    in
    { m = m; c = c; ty = ty }
      
  let add p1 p2 = 
    if rules () = 4 then fprintf fmt "[rule] TR-Arith-Poly plus@.";
    let m = 
      M.fold 
	(fun x a m -> 
	   let a' = (find x m) +/ a in
	   if a' =/ (num_0) then M.remove x m  else M.add x a' m)
	p2.m p1.m
    in 
    { m = m; c = p1.c +/ p2.c; ty = p1.ty }

  let mult_const n p = 
    if n =/ (num_0) then { m = M.empty; c = num_0; ty = p.ty }
    else { p with m = M.map (mult_num n) p.m; c =  n */ p.c }

  let mult_monome a x p  = 
    let ax = { m = M.add x a M.empty; c = (num_0); ty = p.ty} in
    let acx = mult_const p.c ax in
    let m = 
      M.fold
	(fun xi ai m -> M.add (X.mult x xi) (a */ ai) m) p.m acx.m 
    in 
    { acx with m = m}
      
  let mult p1 p2 =
    if rules () = 4 then fprintf fmt "[rule] TR-Arith-Poly mult@.";
    let p = mult_const p1.c p2 in
    M.fold (fun x a p -> add (mult_monome a x p2) p) p1.m p

  let sub p1 p2 =
    if rules () = 4 then fprintf fmt "[rule] TR-Arith-Poly moins@."; 
    add p1 (mult (create [] num_minus_1 p1.ty) p2)

  let div p1 p2 =
    if rules () = 4 then fprintf fmt "[rule] TR-Arith-Poly div@.";
    if M.is_empty p2.m then
      if p2.c =/ num_0 then raise Division_by_zero
      else 
        let p = mult_const (num_1 // p2.c) p1 in
        match M.is_empty p.m, p.ty with
          | true, Ty.Tint  -> {p with c = floor_num p.c}, false 
          | true, Ty.Treal  ->  p, false
          | false, Ty.Tint ->  p, true
          | false, Ty.Treal ->  p, false
          | _ -> assert false
    else raise Maybe_zero


  let modulo p1 p2 =
    if rules () = 4 then fprintf fmt "[rule] TR-Arith-Poly mod@.";
    if M.is_empty p2.m then
      if p2.c =/ num_0 then raise Division_by_zero
      else 
        if M.is_empty p1.m then
	  let c = mod_num p1.c p2.c in
	  let c = if c </ (num_0) then abs_num (p2.c) +/ c else c in
	  { p1 with c = c }
        else raise Not_a_num
    else raise Maybe_zero
      
  let find x p = M.find x p.m

  let is_empty p = M.is_empty p.m

  let choose p =
    let tn= ref None in
    (*version I : prend le premier element de la table*)
    (try M.iter
       (fun x a -> tn := Some (a, x); raise Exit) p.m with Exit -> ());
    (*version II : prend le dernier element de la table i.e. le plus grand 
    M.iter (fun x a -> tn := Some (a, x)) p.m;*)
    match !tn with Some p -> p | _ -> raise Not_found

  let subst x p1 p2 =
    try
      let a = M.find x p2.m in
      add (mult_const a p1) { p2 with m = M.remove x p2.m}
    with Not_found -> p2
      
  let remove x p = { p with m = M.remove x p.m }
      
  let to_list p = map_to_list p.m , p.c

  let type_info p = p.ty

  let is_monomial p  = 
    try 
      M.fold
	(fun x a r -> 
	   match r with
	     | None -> Some (a, x, p.c)
	     | _ -> raise Exit)
	p.m None
    with Exit -> None

  let denominator = function
    | Num.Int _ | Num.Big_int _ -> Big_int.unit_big_int
    | Num.Ratio rat -> Ratio.denominator_ratio rat

  let numerator = function
    | Num.Int i -> Big_int.big_int_of_int i 
    | Num.Big_int b -> b
    | Num.Ratio rat -> Ratio.numerator_ratio rat

  let pgcd_bi a b = Big_int.gcd_big_int a b
      
  let ppmc_bi a b = Big_int.div_big_int (Big_int.mult_big_int a b) (pgcd_bi a b)
     
  let abs_big_int_to_num b =
    let b = 
      try Int (Big_int.int_of_big_int b) 
      with Failure "int_of_big_int" -> Big_int b
    in
    abs_num b
    
  let ppmc_denominators {m=m} = 
    let res =   
      M.fold
        (fun k c acc -> ppmc_bi (denominator c) acc)
        m Big_int.unit_big_int in
    abs_num (num_of_big_int res)

  let pgcd_numerators {m=m} = 
    let res =   
      M.fold
        (fun k c acc -> pgcd_bi (numerator c) acc)
        m Big_int.zero_big_int in
    abs_num (num_of_big_int res)

  let normal_form ({ m = m; c = c } as p) =
    if M.is_empty m then 
      { p with c = num_0 }, p.c, num_1
    else
      let ppcm = ppmc_denominators p in
      let pgcd = pgcd_numerators p in
      let p = mult_const (ppcm // pgcd) p in
      { p with c = num_0 }, p.c, (pgcd // ppcm)

  let normal_form_pos p =
    let p, c, d = normal_form p in
    try
      let a,x = choose p in
      if a >/ num_0 then p, c, d
      else mult_const num_minus_1 p, minus_num c, minus_num d
    with Not_found -> p, c, d

end

