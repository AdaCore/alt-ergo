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

open Num
open Format
open Options

type borne = Strict of (num * Explanation.t) | Large of (num * Explanation.t) 
	     | Pinfty | Minfty

let compare_bornes b1 b2 =
  match b1, b2 with
    | Minfty, Minfty | Pinfty, Pinfty -> 0
    | Minfty, _ | _, Pinfty -> -1
    | Pinfty, _ | _, Minfty -> 1
    | Strict (v1, _), Strict (v2, _) | Large (v1, _), Large (v2, _) 
    | Strict (v1, _), Large (v2, _) | Large (v1, _), Strict (v2, _) -> 
      compare_num v1 v2

let compare_bu_bl b1 b2 =
  match b1, b2 with
    | (Minfty | Pinfty), _ | _,(Minfty | Pinfty) 
    | Strict _, Strict _ | Large _, Large _ -> 
      compare_bornes b1 b2 
    | Strict (v1, _), Large (v2, _) | Large (v1, _), Strict (v2, _) ->
      let c = compare_num v1 v2 in
      if c = 0 then -1 else c
      
let compare_bl_bu b1 b2 =
  match b1, b2 with
    | (Minfty | Pinfty), _ | _,(Minfty | Pinfty) 
    | Strict _, Strict _ | Large _, Large _ -> 
      compare_bornes b1 b2 
    | Strict (v1, _), Large (v2, _) | Large (v1, _), Strict (v2, _) ->
      let c = compare_num v1 v2 in
      if c = 0 then 1 else c

let compare_bl_bl b1 b2 = 
  match b1, b2 with 
    | (Minfty | Pinfty), _ | _,(Minfty | Pinfty) 
    | Strict _, Strict _ | Large _, Large _ -> 
      compare_bornes b1 b2 
    | Strict (v1, _), Large (v2, _) ->
      let c = compare_num v1 v2 in
      if c = 0 then 1 else c
    | Large (v1, _), Strict (v2, _) ->
      let c = compare_num v1 v2 in
      if c = 0 then -1 else c

let compare_bu_bu b1 b2 =
  match b1, b2 with
    | (Minfty | Pinfty), _ | _,(Minfty | Pinfty) 
    | Strict _, Strict _ | Large _, Large _ -> 
      compare_bornes b1 b2 
    | Strict (v1, _), Large (v2, _) ->
      let c = compare_num v1 v2 in
      if c = 0 then -1 else c
    | Large (v1, _), Strict (v2, _) ->
      let c = compare_num v1 v2 in
      if c = 0 then 1 else c

(*      
module SB =
  Set.Make(struct
    type t = (borne * borne)
    let compare (l1,u1) (l2,u2) =
      let cl = compare_bornes l1 l2 in
      if cl <> 0 then cl
      else compare_bornes u1 u2
  end)
  *)

(* module SB =  *)
(*   Set.Make(struct  *)
(*     type t = borne *)
(*     let compare = compare_bornes  *)
(*   end) *)

type t = { 
  ints : (borne * borne) list;
  is_int : bool;
  expl: Explanation.t
}

exception EmptyInterval of Explanation.t
exception NotConsistent of Explanation.t
exception Not_a_float

let print_borne fmt = function
  | Minfty -> fprintf fmt "-inf" 
  | Pinfty -> fprintf fmt "+inf"
  | Strict (v, e) | Large (v, e) ->
    if verbose then fprintf fmt "%s %a" (string_of_num v) Explanation.print e
    else fprintf fmt "%s" (string_of_num v)
      
let print_interval fmt (b1,b2) =
  let c1, c2 = match b1, b2 with
    | Large _, Large _ -> '[', ']'
    | Large _, _ -> '[', '['
    | _, Large _ -> ']', ']'
    | _, _ -> ']', '['
  in 	    
  fprintf fmt "%c%a;%a%c" c1 print_borne b1 print_borne b2 c2
    
let print fmt {ints = ints; is_int = b; expl = e } = 
  List.iter (fun i -> fprintf fmt "%a" print_interval i) ints;
  if verbose then fprintf fmt " %a" Explanation.print e
  

let undefined ty = {
  ints = [Minfty, Pinfty];
  is_int =  ty  = Ty.Tint;
  expl = Explanation.empty
}

let point b ty e = {
  ints = [Large (b, e), Large (b, e)]; 
  is_int = ty  = Ty.Tint;
  expl = Explanation.empty
}

let explain_borne = function
  | Large (_, e) | Strict (_, e) -> e
  | _ -> Explanation.empty

let borne_of k e n = if k then Large (n, e) else Strict (n, e)

let is_point { ints = l; expl = e } =
  match l with
    | [Large (v1, e1) , Large (v2, e2)] when v1 =/ v2 ->
      Some (v1, Explanation.union e2 (Explanation.union e1 e))
    | _ -> None

let check_one_interval b1 b2 is_int =
    match b1, b2 with
      | Pinfty, _ | _, Minfty  -> raise (EmptyInterval Explanation.empty)
      | (Strict (v1, e1) | Large (v1,e1)), (Strict (v2, e2) | Large (v2, e2)) ->
	  let c = compare_num v1 v2 in 
	  if c > 0 then raise 
	    (EmptyInterval (Explanation.union e2 e1));
	  if c = 0 then begin
	    match b1, b2 with
	      | Large _, Large _ when not is_int || is_integer_num v1 ->
		  ()
	      | _ -> raise (EmptyInterval (Explanation.union e2 e1))
	  end
      | _ -> ()

let min_borne b1 b2 = 
  match b1, b2 with
    | Minfty , _ | _ , Minfty -> Minfty
    | b , Pinfty | Pinfty, b -> b
    | (Strict (v1, _) | Large (v1, _)) , (Strict (v2, _) | Large (v2, _)) -> 
	let c = compare_num v1 v2 in
	if c < 0 then b1
	else if c > 0 then b2
	else match b1, b2 with 
	  | (Strict _ as b) , _ | _, (Strict _ as b) -> b
	  | _, _ -> b1
 
let max_borne b1 b2 = 
  match b1, b2 with
    | Pinfty , _ | _ , Pinfty -> Pinfty
    | b , Minfty | Minfty, b -> b
    | (Strict (v1, _) | Large (v1, _)) , (Strict (v2, _) | Large (v2, _)) -> 
	let c = compare_num v1 v2 in
	if c > 0 then b1
	else if c < 0 then b2
	else match b1, b2 with 
	  | (Strict _ as b) , _ | _, (Strict _ as b) -> b
	  | _, _ -> b1
	
let pos_borne b1 =
  compare_bornes b1 (borne_of true Explanation.empty (Int 0)) >= 0
let pos_borne_strict b1 = 
  compare_bornes b1 (borne_of true Explanation.empty (Int 0)) > 0
let neg_borne b1 = 
  compare_bornes b1 (borne_of true Explanation.empty (Int 0)) <= 0
let neg_borne_strict b1 = 
  compare_bornes b1 (borne_of true Explanation.empty (Int 0)) < 0
let zero_borne b1 = 
  compare_bornes b1 (borne_of true Explanation.empty (Int 0)) = 0

exception Found of Sig.answer

let doesnt_contain_0 {ints=l} =
  try
    let max = List.fold_left
      (fun old_u (l, u) -> 
	if neg_borne l && pos_borne u then raise (Found Sig.No);
	if neg_borne_strict old_u && pos_borne_strict l then 
	  raise (Found 
		   (Sig.Yes 
		      (Explanation.union 
			 (explain_borne old_u) (explain_borne l))));
	u) Minfty l in
    if neg_borne_strict max then Sig.Yes (explain_borne max)
    else Sig.No
  with Found ans -> ans

let is_strict_smaller i1 i2 =
  match i1, i2 with
    | _, [] -> false
    | [], _ -> true
    | _ ->
      try
	List.iter2 (fun (l1, u1) (l2, u2) ->
	  if compare_bornes l1 l2 > 0 || compare_bornes u1 u2 < 0
	  then raise Exit
	) i1 i2;
	false
      with 
	| Exit -> true
	| Invalid_argument _ -> List.length i1 > List.length i2

let is_strict_smaller {ints=i1} {ints=i2} = 
  is_strict_smaller i1 i2

(*      
  let inf_greater =
      | (b1,_)::_, (b2,_)::_ ->compare_bornes b1 b2 > 0
  in
  let sup_lesser =
    match List.rev i1, List.rev i2 with
      | _, [] -> false
      | [], _ -> true
      | (_,b1)::_, (_,b2)::_ -> compare_bornes b1 b2 < 0
  in
  inf_greater || sup_lesser
*)

let rec union_bornes l =
  match l with
    | [] | [_] -> l
    | (l1, u1)::((l2, u2)::r as r2) ->
	if compare_bornes u1 l2 < 0 then
	  (l1, u1)::(union_bornes r2)
	else if compare_bornes u1 u2 > 0 then
	  union_bornes ((l1, u1)::r)
	else
	  union_bornes ((l1, u2)::r)

let union ({ints = l} as uints) =
  let l = List.sort (fun (l1, _) (l2, _) -> compare_bornes l1 l2) l in
  { uints with ints = union_bornes l }

let add_borne b1 b2 =
  match b1,b2 with
    | Minfty, Pinfty | Pinfty, Minfty -> assert false
    | Minfty, _ | _, Minfty -> Minfty
    | Pinfty, _ | _, Pinfty -> Pinfty
    | Large (v1, e1), Large (v2, e2) -> 
      Large (v1 +/ v2, Explanation.union e1 e2)
    | (Large (v1, e1) | Strict (v1, e1)), (Large (v2, e2) | Strict (v2, e2)) ->
      Strict (v1 +/ v2, Explanation.union e1 e2)

let add_interval l (b1,b2) =
  List.fold_right
    (fun (b1', b2') l ->
       let l1 = ((add_borne b1 b1'),(add_borne b2 b2'))::l in
       union_bornes (l1)
    ) l []

let add {ints = l1; is_int = is_int; expl = e1} {ints = l2; expl = e2}=
  let l = 
    List.fold_left
      (fun l bs -> let i = add_interval l1 bs in i@l) [] l2 
  in
  union { ints = l ; is_int = is_int; expl = Explanation.union e1 e2 }

let minus_borne = function
  | Minfty -> Pinfty
  | Pinfty -> Minfty
  | Large (v, e) -> Large (minus_num v, e)
  | Strict (v, e) -> Strict (minus_num v, e)

let scale_borne n b =
  assert (n >=/ Int 0);
  if n =/ Int 0 then 
    match b with
    | Pinfty | Minfty -> Large (Int 0, Explanation.empty)
    | Large (_, e) | Strict (_, e) ->  Large (Int 0, e)
  else match b with
    | Pinfty | Minfty -> b
    | Large (v, e) -> Large (n */ v, e)
    | Strict (v, e) -> Strict (n */ v, e)

let scale_interval n (b1,b2) =
  if n </ Int 0 then
    (minus_borne (scale_borne (minus_num n) b2),
     minus_borne (scale_borne (minus_num n) b1))
  else (scale_borne n b1, scale_borne n b2)

(*
let scale_bexpl n be =
  SB.fold (fun (b1,b2) acc ->
    if n >=/ (Int 0) then SB.add ((scale_borne n b1), (scale_borne n b2)) acc
    else SB.add ((scale_borne n b2), (scale_borne n b1)) acc
  ) be SB.empty
  *)

let scale n uints =
  let l = List.map (scale_interval n) uints.ints in
  union { uints with ints = l; expl = uints.expl }
	    
let mult_borne b1 b2 =
  match b1,b2 with
    | Minfty, Pinfty | Pinfty, Minfty -> assert false
    | Minfty, b | b, Minfty ->
	if compare_bornes b (borne_of true Explanation.empty (Int 0)) = 0 then b
	else if pos_borne b then Minfty
	else Pinfty
    | Pinfty, b | b, Pinfty ->
	if compare_bornes b (borne_of true Explanation.empty (Int 0)) = 0 then b
	else if pos_borne b then Pinfty
	else Minfty
    | Strict (v1, e1), Strict (v2, e2) | Strict (v1, e1), Large (v2, e2)
    | Large (v1, e1), Strict (v2, e2) -> 
      Strict (v1 */ v2, Explanation.union e1 e2)
    | Large (v1, e1), Large (v2, e2) -> 
      Large (v1 */ v2, Explanation.union e1 e2)

let mult_borne_inf b1 b2 =
  match b1,b2 with
    | Minfty, Pinfty | Pinfty, Minfty -> Minfty
    | _, _ -> mult_borne b1 b2

let mult_borne_sup b1 b2 =
  match b1,b2 with
    | Minfty, Pinfty | Pinfty, Minfty -> Pinfty
    | _, _ -> mult_borne b1 b2

type interval_class = P | M | N | Z

let class_of (l,u) =
  if zero_borne l && zero_borne u then Z
  else if pos_borne l && pos_borne u then P
  else if neg_borne l && neg_borne u then N
  else M

let mult_bornes (a,b) (c,d) =
  (* see util/intervals_mult.png *)
  match class_of (a,b), class_of (c,d) with
    | P, P -> mult_borne_inf a c, mult_borne_sup b d
    | P, M -> mult_borne_inf b c, mult_borne_sup b d
    | P, N -> mult_borne_inf b c, mult_borne_sup a d
    | M, P -> mult_borne_inf a d, mult_borne_sup b d
    | M, M -> 
      min_borne (mult_borne_inf a d) (mult_borne_inf b c),
      max_borne (mult_borne_sup a c) (mult_borne_sup b d)
    | M, N -> mult_borne_inf b c, mult_borne_sup a c
    | N, P -> mult_borne_inf a d, mult_borne_sup b c
    | N, M -> mult_borne_inf a d, mult_borne_sup a c
    | N, N -> mult_borne_inf b d, mult_borne_sup a c
    | Z, (P | M | N | Z) -> (a, b)
    | (P | M | N ), Z -> (c, d)
      
let rec power_borne_inf p b =
  match p with
    | 1 -> b
    | p -> mult_borne_inf b (power_borne_inf (p-1) b)

let rec power_borne_sup p b =
  match p with
    | 1 -> b
    | p -> mult_borne_sup b (power_borne_sup (p-1) b)

let max_merge b1 b2 =
  let ex = Explanation.union (explain_borne b1) (explain_borne b2) in
  let max = max_borne b1 b2 in
  match max with
    | Minfty | Pinfty -> max
    | Large (v, e) -> Large (v, ex)
    | Strict (v, e) -> Strict (v, ex)

let power_bornes p (b1,b2) =
  if neg_borne b1 && pos_borne b2 then
    match p with
      | 0 -> assert false
      | p when p mod 2 = 0 ->
	  (* max_merge to have explanations !!! *)
	  let m = max_merge (power_borne_sup p b1) (power_borne_sup p b2) in
	  (Large (Int 0, Explanation.empty), m)
      | _ -> (power_borne_inf p b1, power_borne_sup p b2)
  else if pos_borne b1 && pos_borne b2 then
    (power_borne_inf p b1, power_borne_sup p b2)
  else if neg_borne b1 && neg_borne b2 then
    match p with
      | 0 -> assert false
      | p when p mod 2 = 0 -> (power_borne_inf p b2, power_borne_sup p b1)
      | _ -> (power_borne_inf p b1, power_borne_sup p b2)
  else assert false
    
(* let intersect2 (l1, u1) (l2, u2) = (max_borne l1 l2, min_borne u1 u2) *)

let int_of_borne_inf b =
  match b with
    | Minfty | Pinfty -> b
    | Large (v, e) -> Large (ceiling_num v, e)
    | Strict (v, e) ->
	let v' = ceiling_num v in
	if v' >/ v then Large (v', e) else Large (v +/ (Int 1), e) 

let int_of_borne_sup b =
  match b with
    | Minfty | Pinfty -> b
    | Large (v, e) -> Large (floor_num v, e)
    | Strict (v, e) ->
	let v' = floor_num v in
	if v' </ v then Large (v', e) else Large (v -/ (Int 1), e) 

let int_div_of_borne_inf b =
  match b with
    | Minfty | Pinfty -> b
    | Large (v, e) -> Large (floor_num v, e)
    | Strict (v, e) ->
	let v' = floor_num v in
	if v' >/ v then Large (v', e) else Large (v +/ (Int 1), e) 

let int_div_of_borne_sup b =
  match b with
    | Minfty | Pinfty -> b
    | Large (v, e) -> Large (floor_num v, e)
    | Strict (v, e) ->
	let v' = floor_num v in
	if v' </ v then Large (v', e) else Large (v -/ (Int 1), e)

let int_bornes l u = 
  int_of_borne_inf l, int_of_borne_sup u

let int_div_bornes l u = 
  int_div_of_borne_inf l, int_div_of_borne_sup u

(*
let expl_of_bexpl be =
  SB.fold (fun (b1,b2) acc -> 
    let acc = match b1 with
      | Large (_,e1) | Strict (_, e1) -> Explanation.union e1 acc
      | _ -> acc in
    match b2 with
      | Large (_,e2) | Strict (_, e2) -> Explanation.union e2 acc
      | _ -> acc
  ) be Explanation.empty
*)

(*
let intersect_bornes (b1, b2) {ints = l; is_int = is_int; bexpl = bexpl} =
  let l = List.map (intersect2 (b1, b2)) l in
  let l, be = 
    List.fold_right
      (fun (l, u) (l', be) -> try
	 let l,u = if is_int then int_bornes l u else l,u in
	 check_one_interval l u is_int;
	 (l, u)::l', be
       with EmptyInterval be' -> (l', SB.union be be')
      ) l ([], SB.empty) 
  in
  let l = union_bornes l in
  (*debug: 
     let s = if is_strict_smaller l old.ints then "<" else ">=" in
     fprintf fmt "%a %s %a@." print {ints=l;is_int=is_int;expl=expl}
       s print old;
  let e = 
    if is_strict_smaller l old.ints then Explanation.union e expl
    else e in 
  if l = [] then raise (NotConsistent e)
  else *)
  { ints = l; is_int = is_int; bexpl = (SB.union be bexpl) }
*)

(*
let intersect ({ints=l1} as uints1) ({ints=l2} as uints2) =
  (*fprintf fmt "%a inter %a (with %a) = " print uints1 print uints2 Explanation.print expl;*)
  let u =
    List.fold_left
      (fun u' bs ->
	let ui = intersect_bornes bs uints2 in
	{ u' with ints = (u'.ints)@(ui.ints);
	  expl = Explanation.union ui.expl u'.expl }
      ) {ints = []; is_int = uints1.is_int; expl = Explanation.empty}
      uints1.ints in
  let u = union u in
  let e = 
    if is_strict_smaller u uints2 then 
      Explanation.union uints1.expl uints2.expl
    else uints2.expl in
  let u = { u with expl = e } in
  (*fprintf fmt "%a@." print u;*)
  if u.ints = [] then raise (NotConsistent u.expl) else u
*)

(*
let build_relevant_bexpl be bexpl =
  SB.fold (fun (b1, b2) acc ->
    SB.fold (fun (b'1, b'2) acc' ->
      let b = if compare_bornes b2 b'1 < 0 || compare_bornes b1 b'2 > 0 
	then (b'1, b'2)
	else (min_borne b1 b'1, max_borne b2 b'2)
      in
      SB.add b acc') bexpl SB.empty
  ) be SB.empty
*)

let intersect ({ints=l1; expl=e1; is_int=is_int} as uints1) {ints=l2; expl=e2} =
  let rec step (l1,l2) acc expl =
    match l1, l2 with
      | (lo1,up1)::r1, (lo2,up2)::r2 ->
	let (lo1,up1), (lo2,up2) = 
	  if is_int then (int_bornes lo1 up1), (int_bornes lo2 up2)
	  else (lo1,up1), (lo2,up2) in
	let cll = compare_bl_bl lo1 lo2 in
	let cuu = compare_bu_bu up1 up2 in
	let clu = compare_bl_bu lo1 up2 in
	let cul = compare_bu_bl up1 lo2 in
	if cul < 0 then
	  let expl = 
	    (*if r1 <> [] && compare_bu_bl (snd (List.hd r1)) lo2 < 0 then expl
	      else Explanation.union (explain_borne up1) 
	      (Explanation.union (explain_borne lo2) expl) *)
	    if r1 = [] || (r1 <> [] && acc = [] &&
		not (compare_bl_bu lo2 (snd (List.hd r1)) > 0)) then
	      Explanation.union (explain_borne up1) 
		(Explanation.union (explain_borne lo2) expl) 
	    else expl
	  in
	  step (r1, l2) acc expl
	else if clu > 0 then 
	  let expl = 
	    (*if r2 <> [] && compare_bu_bl (snd (List.hd r2)) lo1 < 0 then expl
	      else Explanation.union (explain_borne up2) 
	      (Explanation.union (explain_borne lo1) expl) *)
	    if r2 = [] || (r2 <> [] && acc = [] &&
		not (compare_bl_bu lo1 (snd (List.hd r2)) > 0)) then 
	      Explanation.union (explain_borne up2) 
		(Explanation.union (explain_borne lo1) expl)
	    else expl 
	  in
	  step (l1, r2) acc expl
	else if cll <= 0 && cuu >= 0 then 
	  step (l1, r2) ((lo2,up2)::acc) expl
	else if cll >= 0 && cuu <= 0 then 
	  step (r1, l2) ((lo1,up1)::acc) expl
	else if cll <= 0 && cuu <= 0 && cul >= 0 then 
	  step (r1, l2) ((lo2,up1)::acc) expl
	else if cll >= 0 && cuu >= 0 && clu <= 0 then 
	  step (l1, r2) ((lo1,up2)::acc) expl
	else assert false
      | [], _ | _, [] ->  List.rev acc, expl 
    in
  let l, expl = step (l1,l2) [] (Explanation.union e1 e2) in
  if l = [] then raise (NotConsistent expl)
  else { uints1 with ints = l; expl = expl }


let new_borne_sup expl b ~is_le uints =
  intersect 
    { ints = [Minfty, (borne_of is_le expl b)];
      is_int = uints.is_int;
      expl = Explanation.empty } uints
(* let e =
    if is_strict_smaller new_u uints then Explanation.union expl uints.expl
    else uints.expl in 
  if new_u.ints = [] then raise (NotConsistent (expl_of_bexpl new_u.bexpl))
  else new_u *)

let new_borne_inf expl b ~is_le uints =
  intersect 
    { ints = [(borne_of is_le expl b), Pinfty];
      is_int = uints.is_int;
      expl = Explanation.empty } uints
  (* let e =
     if is_strict_smaller new_u uints then Explanation.union expl uints.expl
    else uints.expl in
  if new_u.ints = [] then raise (NotConsistent (expl_of_bexpl new_u.bexpl))
  else new_u *)


let complement ({ints=l; expl=e} as uints) =
  let rec step l prev acc =
    match l with
      | (b1,b2)::r ->
	let bu = match b1 with
	  | Strict v -> Large v
	  | Large v -> Strict v
	  | _ -> b1 in
	let bl = match b2 with
	  | Strict v -> Large v
	  | Large v -> Strict v
	  | _ -> b2 in
	if bu = Minfty then step r bl acc
	else step r bl ((prev, bu)::acc)
      | [] -> 
	if prev = Pinfty then List.rev acc
	else List.rev ((prev, Pinfty)::acc)
  in
  { uints with ints = step l Minfty [] }
    
(*
let exclude_bornes (b1,b2) ui =
  let bu = match b1 with
    | Strict v -> Large v
    | Large v -> Strict v
    | _ -> b1 in
  let bl = match b2 with
    | Strict v -> Large v
    | Large v -> Strict v
    | _ -> b2 in
  let u1 = intersect_bornes (Minfty, bu) ui in
  let u2 = intersect_bornes (bl, Pinfty) ui in
  let u = {ui with ints = u1.ints@u2.ints;
    expl = Explanation.union u1.expl u2.expl} in
  if u.ints = [] then raise (NotConsistent u.expl) else u
    
let exclude uints1 uints2 =
  let u = 
    union (List.fold_left 
	     (fun u bs ->
	       exclude_bornes bs u) uints2 uints1.ints) in
  let e = 
    if is_strict_smaller u uints2 then 
      Explanation.union uints1.expl uints2.expl
    else uints2.expl in
  let u = { u with expl = e } in
  if u.ints = [] then raise (NotConsistent u.expl) else u
*)

let exclude uints1 uints2 =
  intersect (complement uints1) uints2 

let mult u1 u2 =
  let resl = 
    List.fold_left
      (fun l' (u,l) -> (List.map (mult_bornes (u,l)) u2.ints)@l') 
      [] u1.ints 
  in
  union { ints=resl; is_int = u1.is_int;
	  expl = Explanation.union u1.expl u2.expl }

let power n u =
  let l = List.map (power_bornes n) u.ints in
  union { u with ints = l }


let num_of_float x =
  if x = infinity or x = neg_infinity then raise Not_a_float;
  let (f, n) = frexp x in
  let z =
    Big_int.big_int_of_string
      (Int64.to_string (Int64.of_float (f *. 2. ** 52.))) in
  (*
    Si on a ocaml >= 3.11 on peut mettre (mieux) :
    let z =
      Big_int.big_int_of_int64
        (Int64.of_float (f *. 2. ** 52.)) in
  *)
  let factor = (Int 2) **/ (Int (n - 52)) in
  (Big_int z) */ factor

let root_num a n = 
  if a </ (Int 0) then assert false
  else if a =/ (Int 0) then (Int 0)
  else if n = 2 then num_of_float (sqrt (float_of_num a))
  else num_of_float ((float_of_num a) ** (1./. (float n)))

let root_default_num a n =
  let s = root_num a n in
  let d = a -/ (s **/ (Int n)) in
  if d >=/ (Int 0) then s else a // (s **/ ((Int n) -/ (Int 1)))

let root_exces_num a n =
  let s = root_num a n in
  let d = a -/ (s **/ (Int n)) in
  if d <=/ (Int 0) then s else a // (s **/ ((Int n) -/ (Int 1)))

let root_default_borne is_int x n =
  match x with
    | Pinfty -> Pinfty
    | Minfty -> Minfty
    | Large (v, e) | Strict (v, e) ->
	let s = if v >=/ (Int 0) then root_default_num v n
	else (minus_num (root_exces_num (minus_num v) n)) in
	if is_int then
	  let cs = ceiling_num s in
	  let cs2 = cs **/ (Int n) in
	  if v <=/ cs2 then Large (cs, e)
	  else Large (cs +/ (Int 1), e)
	else Large (s, e)

let root_exces_borne is_int x n =
  match x with
    | Pinfty -> Pinfty
    | Minfty -> Minfty
    | Large (v, e) | Strict (v, e) ->
	let s = if v >=/ (Int 0) then root_exces_num v n
	else (minus_num (root_default_num (minus_num v) n)) in
	if is_int then
	  let cs = floor_num s in
	  let cs2 = cs **/ (Int n) in
	  if v >=/ cs2 then Large (cs, e)
	  else Large (cs -/ (Int 1), e)
	else Large (s, e)

let sqrt_interval is_int (b1,b2) =
  let l1, u1 = (minus_borne (root_exces_borne is_int b2 2),
		minus_borne (root_default_borne is_int b1 2)) in
  let l2, u2 = (root_default_borne is_int b1 2,
		root_exces_borne is_int b2 2) in
  if compare_bornes l1 u1 > 0 then
    if compare_bornes l2 u2 > 0 then []
    else [l2,u2]
  else if compare_bornes l2 u2 > 0 then [l1, u1]
  else  union_bornes [(l1,u1); (l2, u2)]

let root_interval is_int (b1,b2) n =
  let u,l = (root_default_borne is_int b1 n, root_exces_borne is_int b2 n) in
  if compare_bornes u l > 0 then [] else [u,l]

let sqrt {ints = l; is_int = is_int; expl = e } =
  let l =
    List.fold_left
      (fun l' bs ->
	 (sqrt_interval is_int bs)@l'
      ) [] l in
  union { ints = l; is_int = is_int; expl = e }

let rec root n ({ints = l; is_int = is_int; expl = e} as u) =
  if n mod 2 = 0 then root (n/2) (sqrt u)
  else
    let l =
      List.fold_left
	(fun l' bs ->
	  (root_interval is_int bs n)@l'
	) [] l in
    union { ints = l; is_int = is_int; expl = e }
      
let finite_size {ints = l; is_int = is_int} =
  if (not is_int) then None
  else
    try
      let n =
	List.fold_left
	  (fun n (b1,b2) ->
	     match b1, b2 with
	       | Minfty, _ | _, Pinfty -> raise Exit
	       | Large (v1, _) , Large (v2, _) -> n +/ (v2 -/ v1 +/ (Int 1))
	       | _, _ -> assert false
	  ) (Int 0) l in
      Some n
    with Exit -> None
		 
let borne_inf = function
  | {ints = (Large (v, _), _)::_} -> v
  | _ -> invalid_arg "Intervals.borne_inf : No finite lower bound"



let inv_borne_inf b is_int ~other =
  match b with
    | Pinfty -> assert false
    | Minfty ->
      if is_int then Large (Int 0,  explain_borne other) 
      else Strict (Int 0, explain_borne other)
    | Strict (Int 0, e) | Large (Int 0, e) -> Pinfty
    | Strict (v, e) -> Strict (Int 1 // v, e)
    | Large (v, e) -> Large (Int 1 // v, e)

let inv_borne_sup b is_int ~other =
  match b with
    | Minfty -> assert false
    | Pinfty ->
      if is_int then Large (Int 0, explain_borne other)
      else Strict (Int 0, explain_borne other)
    | Strict (Int 0, e) | Large (Int 0, e) -> Minfty
    | Strict (v, e) -> Strict (Int 1 // v, e)
    | Large (v, e) -> Large (Int 1 // v, e)

let inv_bornes (l, u) is_int =
  inv_borne_sup u is_int ~other:l, inv_borne_inf l is_int ~other:u


let inv ({ints=l; is_int=is_int} as u) =
  try
    let l' = List.fold_left 
      (fun acc (l,u) ->
	if (pos_borne_strict l && pos_borne_strict u) 
	  || (neg_borne_strict l && neg_borne_strict u) then 
	  (inv_bornes (l, u) is_int) :: acc
	else raise Exit
      ) [] l in
    union { u with ints=l' }
  with Exit -> { u with ints = [Minfty, Pinfty]  }

let div i1 i2 =
  let inv_i2 = inv i2 in
  if inv_i2.ints = [Minfty, Pinfty] then inv_i2
  else
    let ({ints=l; is_int=is_int} as i) = mult i1 inv_i2 in
    let l = 
      if is_int then 
	List.map (fun (l,u) -> int_div_bornes l u) l
      else l in
    { i with ints = l }

	
