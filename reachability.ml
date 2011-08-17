open Options
open Format
open Sig

module Sy = Symbols
module T  = Term
module A  = Literal
module L  = List

module Make(X : Sig.X) = struct

  type r = X.r
  module Ex = Explanation
  module LR = Literal.Make(struct type t = X.r include X end)

  let todo = false
  let my_print_string s = if todo then print_endline s

  let hreach = Hstring.make "reach"
  let hSome = Hstring.make "Some"
  let hNone = Hstring.make "None"
  let hOption = Hstring.make "option"
  let ty_option ty = Ty.Text ([ty], hOption)

  (* find an option in l *) 
  let rec find_val l =
    match l with
      | [] -> raise Not_found
      | t :: l -> 
	(match T.view t with
	  | {T.f=(Sy.Name (hh, Sy.Other)); T.xs=[e];
	     T.ty=ty} ->
	    if hh = hSome then t, Some e
	    else find_val l
	  | {T.f=(Sy.Name (hh, Sy.Other)); T.xs=[]} ->
	    if hh = hNone then t, None else find_val l
	  | _ -> find_val l)

  (* find a boolean in l *) 
  let rec find_bool l =
    match l with
      | [] -> raise Not_found
      | a :: l -> if T.compare a T.faux = 0 then false, T.faux
	else if T.compare a T.vrai = 0 then true, T.vrai
	else find_bool l

  let make_tr (tst, te1, te2) =
    T.make (Sy.Name (hreach, Sy.Other)) [tst; te1; te2] Ty.Tbool

  let make_b b =
    if b then T.vrai else T.faux

  exception Unsat of Ex.t

  (* Type for reach terms: state -> element1 -> element2 -> rvalue *)
  type rvalue = RKnown of (bool*Ex.t*(T.t*T.t*T.t))
		| RUnknown

  let update_ex_r v ex =
    match v with
      | RUnknown -> RUnknown
      | RKnown (o, e, t) -> RKnown (o, Ex.union e ex, t)

  let merge_rvalue r1 r2 =
    let m r1 r2 : rvalue = match r1, r2 with
      | r, RUnknown 
      | RUnknown, r -> r
      | RKnown (true, ex1, t), RKnown (true, _, _) -> RKnown (true, ex1, t)
      | RKnown (false, ex1, t), RKnown (false, _, _) -> RKnown (false, ex1, t)
      | RKnown (true, ex1, _), RKnown (false, ex2, _)
      | RKnown (false, ex1, _), RKnown (true, ex2, _) ->
	raise (Unsat (Ex.union ex1 ex2)) in
    (m (fst r1) (fst r2), m (snd r1) (snd r2))

  module Renv3 = struct
    include Map.Make(struct type t = X.r include X end)
    let empty e tst te = let v = RKnown (true, Ex.empty, (tst, te, te)) in
			 add e (v, v) empty
    let find e m = try find e m with Not_found -> (RUnknown, RUnknown)
    let add_v e v m = add e (merge_rvalue v (find e m)) m
    let remove_v e m = let _, v2 = find e m in
		       add e (RUnknown, v2) m
  end
  module Renv2 = struct
    include Map.Make(struct type t = X.r include X end)
    let find (tst, te) e  m = try find e m
      with Not_found -> Renv3.empty e tst te
    let add_v (tst, te1, te2) e1 e2 v m = 
      let cluster1 = find (tst, te1) e1 m in
      if e1 = e2 then
	add e1 (Renv3.add_v e1 (v, v) cluster1) m
      else
	let cluster2 = find (tst, te2) e2 m in
	add e1 (Renv3.add_v e2 (v, RUnknown) cluster1)
	  (add e2 (Renv3.add_v e1 (RUnknown, v) cluster2) m)
    let remove_v (tst, te1, te2) e1 e2 m = 
      let cluster1 = find (tst, te1) e1 m in
      let cluster2 = find (tst, te2) e2 m in
      add e1 (Renv3.remove_v e2 cluster1)
	(add e2 (Renv3.remove_v e1 cluster2) m)
  end
  module Renv = struct
    include Map.Make(struct type t = X.r include X end)
    let find st m = try find st m with Not_found -> Renv2.empty
    let add_v (tst, te1, te2) st e1 e2 v m =
      add st (Renv2.add_v (tst, te1, te2) e1 e2 v (find st m)) m
    let remove_v (tst, te1, te2) st e1 e2 m =
      add st (Renv2.remove_v (tst, te1, te2) e1 e2 (find st m)) m
  end

  (* Type for get terms: state*element -> gvalue *)
  type gvalue = GKnown of ((X.r*T.t)option*Ex.t*(T.t*T.t))
		| GUnknown

  let update_ex_f v ex =
    match v with
      | GUnknown -> GUnknown
      | GKnown (o, e, t) -> GKnown (o, Ex.union e ex, t)

  module Genv  = struct
    include Map.Make(struct type t = X.r*X.r
			    let compare (t11,t12) (t21, t22) =
			      let c = X.compare t11 t21 in
			      if c = 0 then X.compare t12 t22
			      else c
    end)
    let find e m = try find e m with Not_found -> GUnknown
  end

  (* Type for set terms: state -> (as result -> uvalue)*(as argument set) *)
  type uvalue = Ex.t*(T.t*T.t*(X.r*T.t) option)

  let update_ex_u (e, t) ex =
    Ex.union e ex, t

  module Uenv = struct
    include Map.Make(struct type t = X.r include X end)
    let find e m = try find e m with Not_found -> T.Map.empty, T.Set.empty
  end

  (* Type for uses *)
  type use = GVal of (T.t*T.t) | RVal of (T.t*T.t*T.t)
	     | UVal of T.t
  module USet  = struct
    include Set.Make(
      struct type t = use
	     let compare u1 u2 =
	       match u1, u2 with
		 | GVal (r11, r12), GVal (r21, r22) ->
		   let c = T.compare r11 r21 in
		   if c = 0 then T.compare r12 r22 else c
		 | GVal _, _ -> -1
		 | _, GVal _ -> 1
		 | RVal (r11, r12, r13), RVal (r21, r22, r23) ->
		   let c = T.compare r11 r21 in
		   if c = 0 then
		     let c = T.compare r12 r22 in
		     if c = 0 then T.compare r13 r23 else c
		   else c
		 | RVal _, _ -> -1
		 | _, RVal _ -> 1
		 | UVal r1, UVal r2 -> T.compare r1 r2
      end)
  end

  (* Type for consequences *)
  type cons = SR of (T.t*T.t*T.t)
	      | SE of (T.t*T.t)

  module Conseq = struct
    type t = bool*cons
    let compare (b1, s1) (b2, s2) =
      if b1 = b2 then
	match s1, s2 with
	  | SE (t11, t12), SE (t21, t22) ->
	    let c = T.compare t11 t21 in
	    if c = 0 then T.compare t12 t22
	    else c
	  | SE _, _ -> -1
	  | _, SE _ -> 1
	  | SR (t11, t12, t13), SR (t21, t22, t23) -> 
	    let c = T.compare t11 t21 in
	    if c = 0 then
	      let c = T.compare t12 t22 in
	      if c = 0 then T.compare t13 t23
	      else c
	    else c
      else if b1 then -1 else 1
    let print fmt (b, s) =
      match s with
	| SE (te1, te2) -> 
	  if b then fprintf fmt "%a = %a" T.print te1 T.print te2
	  else fprintf fmt "%a <> %a" T.print te1 T.print te2
	| SR t -> fprintf fmt "%a = %a" T.print (make_tr t) T.print (make_b b)
    let make_s ts (b, s) =
      match s with
	| SE (te1, te2) ->
	  let e1, ex1 = T.Map.find te1 ts in
	  let e2, ex2 = T.Map.find te2 ts in
	  let ex = Ex.union ex1 ex2 in
	  if b then LR.make (A.Eq (e1, e2)), ex
	  else LR.make (A.Distinct (false, [e1; e2])), ex
	| SR t ->
	  let t = make_tr t in
	  LR.make (A.Eq (X.term_embed t, X.term_embed (make_b b))), Ex.empty
    let make_t (b, s) =
      match s with
	| SE (te1, te2) ->
	  if b then A.LT.make (A.Eq (te1, te2))
	  else A.LT.make (A.Distinct (false, [te1; te2]))
	| SR t ->
	  let t = make_tr t in A.LT.make (A.Eq (t, make_b b))
    let simple are_eq are_neq ts rs (b, s) =
      match s with
	| SE (te1, te2) ->
	  let ex1, ex2 = if b then (are_eq te1 te2, are_neq te1 te2)
	    else (are_neq te1 te2, are_eq te1 te2) in
	  (match ex1, ex2 with
	    | Sig.Yes ex, _ -> Some (true, ex)
	    | _, Sig.Yes ex -> Some (false, ex)
	    | _ -> None)
	| SR (tst, te1, te2) ->
	  let st, _ = T.Map.find tst ts in
	  let e1, _ = T.Map.find te1 ts in
	  let e2, _ = T.Map.find te2 ts in
	  match fst (Renv3.find e2 (Renv2.find (tst, te1) e1
				      (Renv.find st rs))) with
	    | RKnown (bb, ex, _) -> if b = bb then Some (true, ex)
	      else Some (false, ex)
	    | RUnknown -> None
  end

  (* Type for splits *)

  module Split = struct
    include Set.Make (Conseq)
  end

  module SplitSet = struct
    include Set.Make (struct
      type t = Ex.t * Split.t
      let compare (_, s1) (_, s2) = Split.compare s1 s2 end)
    let add_split (ex, l) splits =
      let split = List.fold_left (fun split (b, s) ->
	Split.add (b, s) split) Split.empty l in
      add (ex, split) splits
  end

  (* Type for equality set *)
  module ESet = struct
    include Set.Make (struct 
      type t = (Conseq.t*Ex.t)
      let compare (t1, _) (t2, _) = Conseq.compare t1 t2 end)
    let simple are_eq are_neq ts rs s =
      fold (fun (c, ex) s ->
	match Conseq.simple are_eq are_neq ts rs c with
	  | Some (false, ex1) -> raise (Unsat (Ex.union ex ex1))
	  | Some (true, _) -> s
	  | None -> add (c, ex) s) s empty
  end

  (* Type for the environment *)
  type t =
      {terms : (X.r*Ex.t) T.Map.t;
       st_uses : USet.t T.Map.t;
       e_uses : USet.t T.Map.t;
       gs : gvalue Genv.t;
       f_options : (T.t*T.t) T.Map.t;
       rs : (rvalue*rvalue) Renv3.t Renv2.t Renv.t;
       r_options : (T.t*T.t*T.t) T.Map.t;
       us : (uvalue T.Map.t*T.Set.t) Uenv.t;
       u_options : (T.t*T.t*T.t) T.Map.t;
       split : SplitSet.t}

  let empty _ =
    {terms = T.Map.empty;
     st_uses = T.Map.empty;
     e_uses = T.Map.empty;
     gs = Genv.empty;
     f_options = T.Map.empty;
     rs = Renv.empty;
     r_options = T.Map.empty;
     us = Uenv.empty;
     u_options = T.Map.empty;
     split = SplitSet.empty}

  module Debug = struct

    let assume fmt la = 
      if debug_arrays && la <> [] then begin
        fprintf fmt "++++++[Reach] We assume@.";
        L.iter (fun (a,_,_) -> fprintf fmt "  > %a@." 
          LR.print (LR.make a)) la;
      end

    let print_reachs fmt = Renv.iter 
      (fun st rr ->
	Renv2.iter (fun e1 r ->
	  Renv3.iter (fun e2 k ->
	    if e1 = e2 then ()
	    else
	      (match fst(k) with
		| RUnknown -> ()
		| RKnown (b, ex, _) ->
		  fprintf fmt "reach(%a,%a,%a)  = %a : %a@." X.print st
		    X.print e1 X.print e2 T.print (make_b b) Ex.print ex))
	    r) rr)

    let print_gets fmt = Genv.iter
      (fun (st, e) v ->
	match v with
	  | GUnknown -> ()
	  | GKnown (Some (e3, t3), _, (t1, t2)) ->
	    fprintf fmt "  %a [ %a ] = Some %a@." X.print st X.print e
	      X.print e3
	  | GKnown (None, _, (t1, t2)) ->
	    fprintf fmt "  %a [ %a ] = None@." T.print t1 T.print t2)

    let print_sets fmt = Uenv.iter
      (fun _ (v, _) -> T.Map.iter (fun t _ ->
	fprintf fmt "  %a@." T.print t) v)

    let print_terms fmt = T.Map.iter
      (fun t (r, ex) -> 
	fprintf fmt "  %a -> %a : %a@." T.print t X.print r Ex.print ex)

    let print_used fmt = T.Map.iter
      (fun t v ->
	if USet.is_empty v then fprintf fmt "  %a -> O@." T.print t;
	USet.iter
	  (fun v ->
	    match v with
	      | GVal (st, e) -> fprintf fmt "  %a -> G %a %a@." T.print t
		T.print st T.print e
	      | RVal (st, e1, e2) -> fprintf fmt "  %a -> R %a %a %a@."
		T.print t T.print st T.print e1 T.print e2
	      | UVal st -> fprintf fmt "  %a -> U %a@." T.print t
		T.print st) v)

    let print_splits fmt = 
      SplitSet.iter (fun (ex, s) -> fprintf fmt "%a : %a@."
	(fun fmt -> Split.iter 
	  (fun split -> fprintf fmt "%a " Conseq.print split)) s
	Ex.print ex)

    let env fmt env = 
      if debug_arrays then begin
        fprintf fmt "-- reachs --------------------------------------@.";
        print_reachs fmt env.rs;
        fprintf fmt "-- gets ----------------------------------------@.";
        print_gets fmt env.gs;
        fprintf fmt "-- sets ----------------------------------------@.";
        print_sets fmt env.us;
        fprintf fmt "-- terms ---------------------------------------@.";
        print_terms fmt env.terms;
        (*fprintf fmt "-- uses ---------------------------------------@.";
          print_used fmt env.uses;*)
        fprintf fmt "-- reach splits --------------------------------@.";
        print_splits fmt env.split;
        fprintf fmt "------------------------------------------------@."
      end

    let new_equalities fmt st = 
      if debug_arrays then 
        begin
          fprintf fmt "[Reach] %d implied equalities@."
	    (ESet.cardinal st);
          ESet.iter (fun (a,ex) -> if Ex.empty = ex then ()
	    else fprintf fmt "  %a : %a@."
              Conseq.print a Ex.print ex) st
        end

    let unsat fmt =
      if debug_arrays then 
        begin
          fprintf fmt "[Reach] 1 implied equalities@.";
          fprintf fmt "  false@."
        end
  end

  let update_env_st find tst uses (env, uset) =
    let terms = env.terms in
    try (let ost, _ = T.Map.find tst terms in
	 let st, ex = find tst in
	 if st = ost then env, uset
	 else
	   let env = {env with terms=T.Map.add tst (st, ex) terms} in
	   let env, uset = USet.fold
	     (fun v (env, uset) -> match v with
	       | RVal (_, te1, te2) -> 
		 let e1, _ = T.Map.find te1 terms in
		 let e2, _ = T.Map.find te2 terms in
		 let v, _ = Renv3.find e2 (Renv2.find (tst, te1) e1
					     (Renv.find ost env.rs)) in
		 let rs = Renv.remove_v (tst, te1, te2) ost e1 e2 env.rs in
		 let rs = Renv.add_v (tst, te1, te2)
		   st e1 e2 (update_ex_r v ex) rs in
		 {env with rs=rs}, USet.add (RVal (tst, te1, te2)) uset
	       | GVal (_, te) ->
		 let e, _ = T.Map.find te terms in
		 let v = Genv.find (ost, e) env.gs in
		 if v = Genv.find (st, e) env.gs then
		   env, uset
		 else
		   let gs = Genv.remove (ost, e) env.gs in
		   let gs = Genv.add (st, e) (update_ex_f v ex) gs in
		   {env with gs=gs}, USet.add (GVal (tst, te)) uset
	       | UVal _ ->
		 let ov, os = Uenv.find ost env.us in
		 let v, s = Uenv.find st env.us in
		 let v = T.Map.fold T.Map.add ov v in
		 let v = T.Map.map (fun v -> update_ex_u v ex) v in
		 let us = Uenv.remove ost env.us in
		 let us = Uenv.add st (v, T.Set.union os s) us in
		 {env with us=us}, USet.add (UVal tst) uset
	     ) uses
	     (env, uset) in
	   (env, uset))
    with Not_found ->
      assert false
	
  let update_env_e find te uses (env, uset) =
    let terms = env.terms in
    try (let oe, _ = T.Map.find te terms in
	 let e, ex = find te in
	 if e = oe then env, uset
	 else
	   let env = {env with terms=T.Map.add te (e, ex) terms} in
	   let env, uset = USet.fold
	     (fun v (env, uset) -> match v with
	       | GVal (tst, te1) ->
		 let st, _ = T.Map.find tst terms in
		 if te <> te1 then
		   let e1, _ = T.Map.find te1 terms in
		   let v = Genv.find (st, e1) env.gs in
		   match v with
		     | GKnown (Some (_, t), exx, tt) ->
		       let v = GKnown (Some (e, t), Ex.union ex exx, tt) in
		       let gs = Genv.add (st, e1) v env.gs in
		       {env with gs=gs}, USet.add (GVal (tst, te1)) uset
		     | _ -> failwith "erreur uf";
		 else
		   (let v = Genv.find (st, oe) env.gs in
		    let gs = Genv.remove (st, oe) env.gs in
		    let gs = Genv.add (st, e) (update_ex_f v ex) gs in
		    {env with gs=gs}, USet.add (GVal (tst, te)) uset)
	       | RVal (tst, te1, te2) ->
		 let st, _ = T.Map.find tst terms in 
		 if te1 <> te then
		   (let e1 , _= T.Map.find te1 terms in
		    let v, _ = Renv3.find oe (Renv2.find (tst, te1) e1 
						(Renv.find st env.rs)) in
		    let rs = Renv.remove_v (tst, te1, te2) st e1 oe env.rs in
		    let rs = Renv.add_v (tst, te1, te2)
		      st e1 e (update_ex_r v ex) rs in
		    {env with rs=rs}, USet.add (RVal (tst, te1, te2)) uset)
		 else if te2 <> te then
		   (let e2, _ = T.Map.find te2 terms in
		    let v, _ = Renv3.find e2 (Renv2.find (tst, te1) oe
						(Renv.find st env.rs)) in
		    let rs = Renv.remove_v (tst, te1, te2) st oe e2 env.rs in
		    let rs = Renv.add_v (tst, te1, te2)
		      st e e2 (update_ex_r v ex) rs in
		    {env with rs=rs}, USet.add (RVal (tst, te, te2)) uset)
		 else 
		   (let v, _ = Renv3.find oe (Renv2.find (tst, te1) oe
						(Renv.find st env.rs)) in
		    let rs = Renv.remove_v (tst, te1, te2) st oe oe env.rs in
		    let rs = Renv.add_v (tst, te1, te2)
		      st e e (update_ex_r v ex) rs in
		    {env with rs=rs}, USet.add (RVal (tst, te, te)) uset)
	       | _ -> assert false
	     ) uses
	     (env, uset) in
	   (env, uset))
    with Not_found ->
      assert false 

  (* ANTISYMMETRY : If R(st, e1, e2)=true and R(st, e2, e1)=true,
     assume e1 = e2 *)
  let handle_antisym (_, te1, te2) ex1 v acc =
    match v with
      | RKnown (true, ex2, _) ->
	  let exx = Ex.union ex1 ex2 in
	  ESet.add ((true, SE (te1, te2)), exx) acc
      | _ -> acc 

  (* TRANSITIVITY : If R(st, e1, e2)=true, for all R(st, e3, e1)=true, assume
     R(st, e3, e2)=true, and, for all R(st, e2, e3)=true assume
     R(st, e1, e3)=rue *)
  let handle_trans r1 r2 (e1, e2) (tst, te1, te2) ex1 acc =
    let acc = Renv3.fold (fun e3 (_, v) acc ->
      match v with
	| RKnown (true, ex2, (_, te3, _)) ->
	  if e1 = e3 || e3 = e2 then
	    acc
	  else
	    (let ex = Ex.union ex1 ex2 in
	     let res = (true, SR (tst, te3, te2)) in
	     ESet.add (res, ex) acc)
	| _ -> acc) r1 acc in
    Renv3.fold (fun e3 (v, _) acc ->
      match v with
	| RKnown (true, ex2, (_, _, te3)) ->
	  if e1 = e3 || e3 = e2 then
	    acc
	  else
	    (let ex = Ex.union ex1 ex2 in
	     let res = (true, SR (tst, te1, te3)) in
	     ESet.add (res, ex) acc)
	| _ -> acc) r2 acc

  (* ORDERING : If R(st, e1, e2)=true, for all R(st, e1, e3)=true, assume
     either R(st, e3, e2)=true or R(st, e2, e3)=true *)
  let handle_order r1 r2 (st, e1, e2) (tst, te1, te2) ex1
      splits =
    Renv3.fold (fun e3 (v, _) splits ->
      match v with
	| RKnown (true, ex, (_, _, te3)) ->
	  let ex = Ex.union ex1 ex in
	  if e1 = e3 || e3 = e2 then
	    splits
	  else
	    (let res = [(true, SR (tst, te2, te3));
			(true, SR (tst, te3, te2))] in
	     let splits = SplitSet.add_split (ex, res) splits in
	     splits)
	| _ -> splits
    ) r1 splits

  (* REACH1 : If st[e1] = Some e2, assume R(st, e1, e2)=true *)
  let handle_reach1 r ex (st, e, res) (tst, te)
      assume =
    match res with
      | None -> assume
      | Some (e2, te2) -> 
	let res = true, SR (tst, te, te2) in
	ESet.add (res, ex) assume

  (* REACH2 : If R(st, e1, e2)=true and st[e1] = None, assume e1 = e2
     and if st[e1] = Some e3, assume either e1 = e2 or R(st, e3, e2)=true *)
  let handle_reach2 r ex (st, e1, e2, res) (tst, te1, te2)
      assume splits =
    (* e1 = e2 nothing to do *)
    if e1 = e2 then splits, assume
    else
       match res with
	 (* k = None -> e1 = e2 *)
	 | None ->
	       let res = true, SE (te1, te2) in
	       splits, ESet.add (res, ex) assume
	 (* k = Some e3 -> e1 = e2 \/ R(st, e3, e2)=true *)
	 | Some (e3, te3) ->
	   let res = [(true, SE (te1, te2)); (true, SR (tst, te3, te2))] in
	   let splits = SplitSet.add_split (ex, res) splits in
	   splits, assume

  let rhandle_reach2 f r ex (st, e1, e2) (tst, te1, te2)
      assume splits =
    match Genv.find (st, e1) f with
      | GUnknown -> splits, assume
      | GKnown (res, ex2, _) ->
	handle_reach2 r (Ex.union ex ex2) (st, e1, e2, res)
	  (tst, te1, te2) assume splits

  let fhandle_reach2 map r ex (st, e1, res) (tst, te1)
      assume splits =
    Renv3.fold (fun e2 (v, _) (splits, assume) ->
      match v with
	| RKnown (true, ex1, (_, _, te2)) -> 
	  let r = Renv2.find (tst, te2) e2 map in
	  handle_reach2 r (Ex.union ex ex1) (st, e1, e2, res)
	    (tst, te1, te2) assume splits
	| _ -> splits, assume) r
      (splits, assume)

  (* WELL-FOUNDED : If st[e1] = Some e3 and R(st, e2, e1)=true
     then assume e3 <> e2 *)
  let handle_wf ex (res, e2, te2) assume =
    match res with
      | None -> assume
      | Some (e3, te3) ->
	    let eq = false, SE (te3, te2) in
	    (ESet.add (eq, ex) assume)
	      
  let rhandle_wf f ex (st, e1, e2) (_, te1, _) assume =
    match Genv.find (st, e2) f with
      | GUnknown -> assume
      | GKnown (res, ex2, _) ->
	handle_wf (Ex.union ex ex2) (res, e1, te1) assume

  let fhandle_wf r ex (st, e, res) assume =
    match res with
      | None -> assume
      | Some (e2, _) ->
	match snd(Renv3.find e2 r) with
	  | RKnown (true, ex2, _) ->
	    raise (Unsat (Ex.union ex ex2))
	  | RKnown (false, _, _) -> assume
	  | RUnknown ->
	    Renv3.fold (fun e3 (_, v) acc ->
	      match v with
		| RKnown (true, ex2, (_, te3, _)) ->
		  handle_wf (Ex.union ex ex2) (res, e3, te3) acc
		| _ -> acc) r assume

  (* st[e1 <- Some (e2)] -> - R (st, e2, e1) *)
  let handle_wrong_update rs ex (st, e1, e2) (tst, te1, te2) assume =
    let res = false, SR (tst, te2, te1) in
    ESet.add (res, ex) assume

  (* R (st[e1 <- Some (e2)], x1, x2) ->
     R (st, x1, e1) -> e1 = x2 \/ R (st, x1, x2)/\- R (st, e1, x2) \/
     R (st, e2, x2)
     - R (st, x1, e1) -> R (st, x1, x2) *)
  let handle_update_Some rs ex (tst, te1, te2, tx1, tx2) acc =
    let res1 = [(true, SE (te1, tx2)); (true, SR (tst, te2, tx2));
		(false, SR (tst, tx1, te1))] in
    let res2 = (false, SR (tst, te1, tx2)) :: res1 in
    let res1 = (true, SR (tst, tx1, tx2)) :: res1 in
    let res3 = [(true, SR (tst, tx1, te1)); (true, SR (tst, tx1, tx2))] in
    let acc = SplitSet.add_split (ex, res1) acc in
    let acc = SplitSet.add_split (ex, res2) acc in
    let acc = SplitSet.add_split (ex, res3) acc in
    acc

  (* R (st[e <- None], x1, x2) ->
     R (st, x1, e) -> e = x2 \/ R (st, x1, x2)/\- R (st, e, x2)
     - R (st, x1, e) -> R (st, x1, x2) *)
  let handle_update_None rs ex (tst, te, tx1, tx2) acc =
    let res1 = [(true, SE (te, tx2)); (false, SR (tst, tx1, te))] in
    let res2 = (false, SR (tst, te, tx2)) :: res1 in
    let res1 = (true, SR (tst, tx1, tx2)) :: res1 in
    let res3 = [(true, SR (tst, tx1, te)); (true, SR (tst, tx1, tx2))] in
    let acc = SplitSet.add_split (ex, res1) acc in
    let acc = SplitSet.add_split (ex, res2) acc in
    let acc = SplitSet.add_split (ex, res3) acc in
    acc

  let uhandle_update_Some rs ex st2 (tst, te1, te2) splits =
    let m = Renv.find st2 rs in
    Renv2.fold (fun _ r acc -> Renv3.fold (fun _ (v, _) acc ->
	match v with
	  | RKnown (true, ex1, (_, tx1, tx2)) ->
	    let ex = Ex.union ex ex1 in
	    handle_update_Some rs ex (tst, te1, te2, tx1, tx2) acc
	  | _ -> acc) r acc) m splits

  let uhandle_update_None rs ex st2 (tst, te) splits =
    let m = Renv.find st2 rs in
    Renv2.fold (fun _ r acc -> Renv3.fold (fun _ (v, _) acc ->
	match v with
	  | RKnown (true, ex1, (_, tx1, tx2)) ->
	    let ex = Ex.union ex ex1 in
	    handle_update_None rs ex (tst, te, tx1, tx2) acc
	  | _ -> acc) r acc) m splits

  let rhandle_update ts rs us ex (st, x1, x2)
      (_, tx1, tx2) splits =
    try (let v, _ = Uenv.find st us in 
	 T.Map.fold (fun _ (ex1, (tst, te1, tk)) acc ->
	     let ex = Ex.union ex ex1 in
	     match tk with
	       | Some (_, te2) ->
		 handle_update_Some rs ex 
		   (tst, te1, te2, tx1, tx2) acc
	       | None -> 
		 handle_update_None rs ex
		   (tst, te1, tx1, tx2) acc) v
	   splits)
    with Not_found -> assert false

  (* R (st, x1, x2), st[e <- k] ->
     R (st, e, x2) /\ R (st, x1, e) \/ R (st[e <- k], x1, x2) *)
  let uhandle_update_inv_1 m ex tst1 tst2 te acc =
    Renv2.fold (fun _ r_x1 acc ->
      Renv3.fold (fun _ (v, _) acc ->
	match v with
	  | RKnown (true, ex1, (_, tx1, tx2)) ->
	    let ex = Ex.union ex1 ex in
	    let res = [(true, SR (tst2, tx1, tx2))] in
	    let res1 = (true, SR (tst1, te, tx2)) :: res in
	    let res2 = (true, SR (tst1, tx1, te)) :: res in
	    SplitSet.add_split (ex, res1) (SplitSet.add_split (ex, res2) acc)
	  | _ -> acc) r_x1 acc) m acc
    
  (* R (st, x, e), st[e <- k] -> R (st[e <- k], x, e) *)
  let uhandle_update_inv_2 m ex tst1 tst2 e te assume =
    let re = Renv2.find (tst1, te) e m in
    Renv3.fold (fun _ (_, v) acc ->
      match v with
	| RKnown (true, ex1, (_, tx, _)) ->
	  let ex = Ex.union ex ex1 in
	  let res = true, SR (tst2, tx, te) in
	  ESet.add (res, ex) acc
	| _ -> acc) re assume

  (* R (st, x1, x2), R (st, e2, x2), st[e1 <- Some e2] ->
     R (st[e <- k], x1, x2) *)
  let uhandle_update_inv_3 m ex tst1 tst2 (e1, e2) (te1, te2) assume =
    let re2 = Renv2.find (tst1, te2) e2 m in
    Renv3.fold (fun x2 (v, _) acc ->
      match v with
	| RKnown (true, ex1, (_, _, tx2)) ->
	  let rx2 = Renv2.find (tst1, tx2) x2 m in
	  let ex = Ex.union ex ex1 in
	  Renv3.fold (fun _ (_, v) acc ->
	    match v with
	      | RKnown (true, ex1, (_, tx1, _)) ->
		let ex = Ex.union ex ex1 in
		let res = true, SR (tst2, tx1, tx2) in
		ESet.add (res, ex) acc
	      | _ -> acc) rx2 acc
	| _ -> acc) re2 assume

  (* R (st, x1, e1), R (st, e2, x2), st[e <- Some e2] ->
     R (st[e <- k], x1, x2) *)
  let uhandle_update_inv_4 m ex tst1 tst2 (e1, e2) (te1, te2) assume =
    let re2 = Renv2.find (tst1, te2) e2 m in
    Renv3.fold (fun _ (v, _) acc ->
      match v with
	| RKnown (true, ex1, (_, _, tx2)) ->
	  let re1 = Renv2.find (tst1, te1) e1 m in
	  let ex = Ex.union ex ex1 in
	  Renv3.fold (fun _ (_, v) acc ->
	    match v with
	      | RKnown (true, ex1, (_, tx1, _)) ->
		let ex = Ex.union ex ex1 in
		let res = true, SR (tst2, tx1, tx2) in
		ESet.add (res, ex) acc
	      | _ -> acc) re1 acc
	| _ -> acc) re2 assume

  let uhandle_update_inv_Some rs ex tst1 tst2 (st, e1, e2)
      (te1, te2) assume =
    let m = Renv.find st rs in
    let assume = 
      uhandle_update_inv_3 m ex tst1 tst2 (e1, e2) (te1, te2) assume in
    let assume = 
      uhandle_update_inv_4 m ex tst1 tst2 (e1, e2) (te1, te2) assume in
    assume

  let uhandle_update_inv rs ex tst1 tst2 (st, e) te k assume splits =
    let m = Renv.find st rs in
    let splits = 
      uhandle_update_inv_1 m ex tst1 tst2 te splits in
    let assume = 
      uhandle_update_inv_2 m ex tst1 tst2 e te assume in
    splits, assume

  (* R (st, x1, x2), st[e <- k] ->
      R (st, x1, e) /\ R (st, e, x2) \/ R (st[e <- k], x1, x2) *)
  let rhandle_update_inv_1 m ex tst1 tst2 (_, te) (x1, tx1) (x2, tx2) acc =
    let res = [(true, SR (tst2, tx1, tx2))] in
    let res1 = (true, SR (tst1, te, tx2)) :: res in
    let res2 = (true, SR (tst1, tx1, te)) :: res in
    SplitSet.add_split (ex, res1) (SplitSet.add_split (ex, res2) acc)

  (* R (st, x, e), st[e <- k] -> R (st[e <- k], x, e) *)
  let rhandle_update_inv_2 m ex _ tst2 (e, _) (x, tx) (ee, te) assume =
    if e = ee then
      let res = true, SR (tst2, tx, te) in
      ESet.add (res, ex) assume
    else assume

  (* R (st, x1, x2), R (st, e2, x2), st[e1 <- Some e2] ->
     R (st[e <- k], x1, x2) *)
  let rhandle_update_inv_31 m ex tst1 tst2 (_, _) (e2, te2) (x1, tx1) (x2, tx2)
      assume =
    let re2 = Renv2.find (tst1, te2) e2 m in
    match fst (Renv3.find x2 re2) with
      | RKnown (false, ex1, _) ->
	let ex = Ex.union ex ex1 in
	let res = true, SR (tst2, tx1, tx2) in
	ESet.add (res, ex) assume
      | _ -> assume

  (* R (st, x1, x2), R (st, e2, x2), st[e1 <- Some e2] ->
     R (st[e <- k], x1, x2) *)
  let rhandle_update_inv_32 m ex tst1 tst2 (_, _) (e2, _) (ee2, _) (x2, tx2)
      assume =
    if e2 = ee2 then
      let rx2 = Renv2.find (tst1, tx2) x2 m in
      Renv3.fold (fun _ (_, v) acc ->
	match v with
	  | RKnown (true, ex1, (_, tx1, _)) ->
	    let ex = Ex.union ex ex1 in
	    let res = true, SR (tst2, tx1, tx2) in
	    ESet.add (res, ex) acc
	  | _ -> acc) rx2 assume
    else assume

  (* R (st, x1, e1), R (st, e2, x2), st[e <- Some e2] ->
     R (st[e <- k], x1, x2) *)
  let rhandle_update_inv_41 m ex tst1 tst2 (e1, _) (e2, te2) (x1, tx1) (ee1, _)
      assume  =
    if e1 = ee1 then
      let re2 = Renv2.find (tst1, te2) e2 m in
      Renv3.fold (fun _ (v, _) acc ->
	match v with
	  | RKnown (true, ex1, (_, _, tx2)) ->
	    let ex = Ex.union ex ex1 in
	    let res = true, SR (tst2, tx1, tx2) in
	    ESet.add (res, ex) acc
	  | _ -> acc) re2 assume
    else assume

  (* R (st, x1, e1), R (st, e2, x2), st[e <- Some e2] ->
     R (st[e <- k], x1, x2) *)
  let rhandle_update_inv_42 m ex tst1 tst2 (e1, te1) (e2, _) (ee2, _) (x2, tx2)
      assume  =
    if e2 = ee2 then
      let re1 = Renv2.find (tst1, te1) e1 m in
      Renv3.fold (fun _ (_, v) acc ->
	match v with
	  | RKnown (true, ex1, (_, tx1, _)) ->
	    let ex = Ex.union ex ex1 in
	    let res = true, SR (tst2, tx1, tx2) in
	    ESet.add (res, ex) acc
	  | _ -> acc) re1 assume
    else assume

  let rhandle_update_inv_t rs us ts ex (st, x1, x2) (tst, tx1, tx2)
      assume splits =
    let m = Renv.find st rs in
    let _, s = Uenv.find st us in
    T.Set.fold (fun st2 (splits, assume) ->
      let st2, ex1 =  T.Map.find st2 ts in
      let ex = Ex.union ex ex1 in
      let v, _ = Uenv.find st2 us in
      T.Map.fold (fun tst2 (ex1, (tst1, te, k)) (splits, assume) ->
	let ex = Ex.union ex ex1 in
	let st1, ex1 = T.Map.find tst1 ts in
	if st1 = st then
	  let ex = Ex.union ex ex1 in
	  let e, ex1 = T.Map.find te ts in
	  let ex = Ex.union ex ex1 in
	  let splits = rhandle_update_inv_1 m ex tst1 tst2 (e, te) 
	    (x1, tx1) (x2, tx2) splits in
	  let assume = rhandle_update_inv_2 m ex tst1 tst2 (e, te) (x1, tx1) 
	    (x2, tx2) assume in
	  match k with
	    | None -> splits, assume
	    | Some (e2, te2) ->
	      let assume = rhandle_update_inv_31 m ex tst1 tst2 (e, te) 
		(e2, te2) (x1, tx1) (x2, tx2) assume in
	      let assume = rhandle_update_inv_32 m ex tst1 tst2 (e, te) 
		(e2, te2) (x1, tx1) (x2, tx2) assume in
	      let assume = rhandle_update_inv_41 m ex tst1 tst2 (e, te) 
		(e2, te2) (x1, tx1) (x2, tx2) assume in
	      let assume = rhandle_update_inv_42 m ex tst1 tst2 (e, te) 
		(e2, te2) (x1, tx1) (x2, tx2) assume in
	      splits, assume
	else splits, assume) v (splits, assume)) s (splits, assume)

  let r_add_conseq st e1 e2 (b, exp, (tst, te1, te2 as term)) env
      assume =
    let m = Renv.find st env.rs in
    let cluster1 = Renv2.find (tst, te1) e1 m in
    let cluster2 = Renv2.find (tst, te2) e2 m in
    let (_, v2) = Renv3.find e2 cluster1 in
    if b then
      if e1 = e2 then
	assume, env.split
      else
	let assume = handle_antisym term exp v2
	  assume in
	let assume = handle_trans cluster1 cluster2 (e1, e2) term
	  exp assume in
	let splits = handle_order cluster1 cluster2 
	  (st, e1, e2) term exp env.split in
	let splits, assume = rhandle_reach2
	  env.gs cluster2 exp (st, e1, e2) term assume splits in
	let assume = rhandle_wf env.gs exp (st, e1, e2) term assume in
	let splits = rhandle_update env.terms
	  env.rs env.us exp (st, e1, e2) term splits in
	let splits, assume = rhandle_update_inv_t env.rs env.us env.terms exp
	  (st, e1, e2) term assume splits in
	assume, splits
    else
      assume, env.split

  let add_R_val find (b, exp, (tst, te1, te2)) env assume =
    let terms, st_uses, e_uses = env.terms, env.st_uses, env.e_uses in
    let v = RVal (tst, te1, te2) in
    let exp, st, st_uses, terms = 
      try (let st, ex = T.Map.find tst terms in
	   let ust = T.Map.find tst st_uses in
	   Ex.union ex exp, st, T.Map.add tst (USet.add v ust) st_uses, terms)
      with Not_found -> 
	let st, ex = find tst in
	Ex.union ex exp, st, T.Map.add tst (USet.singleton v) st_uses,
	T.Map.add tst (st, ex) terms in
    let exp, e1, e_uses, terms = 
      try (let e1, ex = T.Map.find te1 terms in
	   let ue = T.Map.find te1 e_uses in
	   Ex.union ex exp, e1, T.Map.add te1 (USet.add v ue) e_uses, terms)
      with Not_found -> 
	let e1, ex = find te1 in
	Ex.union ex exp, e1, T.Map.add te1 (USet.singleton v) e_uses,
	T.Map.add te1 (e1, ex) terms in
    let exp, e2, e_uses, terms = 
      try (let e2, ex = T.Map.find te2 terms in
	   let ue = T.Map.find te2 e_uses in
	   Ex.union ex exp, e2, T.Map.add te2 ue e_uses, terms)
      with Not_found -> 
	let e2, ex = find te2 in
	Ex.union ex exp, e2, T.Map.add te2 (USet.singleton v) e_uses,
	T.Map.add te2 (e2, ex) terms in
    let m = Renv.find st env.rs in
    let cluster1 = Renv2.find (tst, te1) e1 m in
    let (v1, v2) = Renv3.find e2 cluster1 in
    match v1 with
      | RKnown (bb, ex, _) -> if b = bb then (env, assume)
	else raise (Unsat (Ex.union exp ex))
      | RUnknown ->
	let v = (b, exp, (tst, te1, te2)) in
	let rs = Renv.add_v (tst, te1, te2) st e1 e2 (RKnown v) env.rs in
	let env = {env with rs=rs; terms=terms; st_uses=st_uses;
	  e_uses=e_uses} in
	let assume, split =
	  r_add_conseq st e1 e2 v env assume in
	{env with split=split}, assume

  let add_R find class_of are_eq are_neq t (tst, te1, te2) env assume =
    try (
      let b, tt = find_bool (class_of t) in
      let ex = match are_eq t tt with
	| Sig.No -> assert false
	| Sig.Yes ex -> ex in
      add_R_val find (b, ex, (tst, te1, te2)) env assume)
    with Not_found ->
      ({env with r_options=T.Map.add t (tst, te1, te2) env.r_options}, assume)


  let f_add_conseq st e (res, ex, (tst, te)) env
      assume =
    let map = Renv.find st env.rs in
    let r = Renv2.find (tst, te) e map in
    let assume =
      handle_reach1 r ex (st, e, res) (tst, te)
	assume in
    let (splits, assume) = 
      fhandle_reach2 map r ex (st, e, res) (tst, te)
	assume env.split in
    let assume = fhandle_wf r ex (st, e, res) assume in
    assume, splits

  let add_F_val find (res, ex, (tst, te)) env assume =
    let terms, st_uses, e_uses = env.terms, env.st_uses, env.e_uses in
    let v = GVal (tst, te) in
    let ex, st, st_uses, terms = 
      try (let st, ex1 = T.Map.find tst terms in
	   let ust = T.Map.find tst st_uses in
	   Ex.union ex ex1, st, T.Map.add tst (USet.add v ust) st_uses, terms)
      with Not_found -> 
	let st, ex1 = find tst in
	Ex.union ex ex1, st, T.Map.add tst (USet.singleton v) st_uses,
	T.Map.add tst (st, ex1) terms in
    let ex, e, e_uses, terms = 
      try (let e, ex1 = T.Map.find te terms in
	   let ue = T.Map.find te e_uses in
	   Ex.union ex ex1, e, T.Map.add te (USet.add v ue) e_uses, terms)
      with Not_found -> 
	let e, ex1 = find te in
	Ex.union ex ex1, e, T.Map.add te (USet.singleton v) e_uses, 
	T.Map.add te (e, ex1) terms in
    let ex, res, e_uses, terms = match res with
      | None -> ex, None, e_uses, terms
      | Some te -> 
	let ex, e, uses, terms =
	  try (let e, ex1 = T.Map.find te terms in
	       let ue = T.Map.find te e_uses in
	       Ex.union ex ex1, e, T.Map.add te (USet.add v ue) e_uses, terms)
	  with Not_found ->
	    let e, ex1 = find te in
	    Ex.union ex ex1, e, T.Map.add te (USet.singleton v) e_uses,
	    T.Map.add te (e, ex1) terms in
	ex, Some (e, te), uses, terms in
    match Genv.find (st, e) env.gs with
      | GKnown _ -> (env, assume)
      | GUnknown ->
	let v = (res, ex, (tst, te)) in
	let env = {env with terms=terms; st_uses=st_uses; e_uses=e_uses} in
	let assume, split = 
	  f_add_conseq st e v env assume in
	let gs = Genv.add (st, e) (GKnown v) env.gs in
	let env = {env with gs = gs; split=split} in
	(env, assume)

  let add_F find class_of are_eq are_neq (t, tst, te) env assume =
    try (
      let tt, res = find_val (class_of t) in
      let ex = 
	match are_eq t tt with
	  | Sig.No -> assert false
	  | Sig.Yes ex -> ex in
      add_F_val find (res, ex, (tst, te)) env assume)
    with Not_found ->
      ({env with f_options=T.Map.add t (tst, te) env.f_options}, assume)

  let u_add_conseq (st2, st1, e) t (ex, (tst, te, tk)) env assume =
    let splits = env.split in
    let splits, assume =
      uhandle_update_inv env.rs ex tst t (st1, e) te tk assume splits in
    match tk with
      | None -> 
	uhandle_update_None env.rs ex st2 (tst, te) splits, assume
      | Some (e2, te2) ->
	let assume =
	  handle_wrong_update env.rs ex (st1, e, e2) (tst, te, te2) assume
	in
	let splits =
	  uhandle_update_Some env.rs ex st2
	    (tst, te, te2) splits in
	let assume = uhandle_update_inv_Some env.rs ex tst t (st1, e, e2) 
	  (te, te2) assume in
	splits, assume

  let add_U_val find (t, ex, (tst, te, tk)) env assume =
    let terms, st_uses, e_uses = env.terms, env.st_uses, env.e_uses in
    let v = UVal t in
    let ex, st2, st_uses, terms = 
      try (let st, ex1 = T.Map.find t terms in
	   let ust = T.Map.find t st_uses in
	   Ex.union ex ex1, st, T.Map.add t (USet.add v ust) st_uses, terms)
      with Not_found -> 
	let st, ex1 = find t in
	Ex.union ex ex1, st,  T.Map.add t (USet.singleton v) st_uses, 
	T.Map.add t (st, ex1) terms in
    let ex, st1, st_uses, terms = 
      try (let st, ex1 = T.Map.find tst terms in
	   Ex.union ex ex1, st, st_uses, terms)
      with Not_found -> 
	let st, ex1 = find tst in
	Ex.union ex ex1, st,T.Map.add tst USet.empty st_uses,
	T.Map.add tst (st, ex1) terms in
    let ex, e, e_uses, terms =
      try (let e, ex1 = T.Map.find te terms in
	   Ex.union ex ex1, e, e_uses, terms)
      with Not_found -> 
	let e, ex1 = find te in
	Ex.union ex ex1, e, T.Map.add te USet.empty e_uses,
	T.Map.add te (e, ex1) terms in
    let ex, k, terms, e_uses = match tk with
      | None -> ex, None, terms, e_uses
      | Some te -> 
	let ex, e, terms, e_uses = 
	  try (let e, ex1 = T.Map.find te terms in
	       Ex.union ex ex1, e, terms, e_uses)
	  with Not_found -> 
	    let e, ex1 = find te in
	    Ex.union ex ex1, e, T.Map.add te (e, ex1) terms,
	    T.Map.add te USet.empty e_uses in
	ex, Some (e, te), terms, e_uses in
    let uvals, uterms = Uenv.find st2 env.us in
    if T.Map.mem t uvals then (env, assume)
    else
      let v = (ex, (tst, te, k)) in
      let env = {env with terms = terms; st_uses = st_uses; e_uses=e_uses} in
      let split, assume = 
	u_add_conseq (st2, st1, e) t v env assume in
      let us = Uenv.add st2 (T.Map.add t v uvals, uterms)
	env.us in
      let us = Uenv.add st1 (match Uenv.find st1 us with
	| v, s -> v, T.Set.add t s) us in
      let env = {env with us = us; split=split} in
      (env, assume)

  let add_U find class_of are_eq are_neq (t, (tst, te, tk)) env assume =
    try (
      let tt, res = find_val (class_of tk) in
      let ex =
	match are_eq tk tt with
	  | Sig.No -> assert false
	  | Sig.Yes ex -> ex in
      add_U_val find (t, ex, (tst, te, res)) env assume)
    with Not_found ->
      ({env with u_options=T.Map.add t (tst, te, tk) env.u_options},
       assume)

  exception No_cons of (ESet.t)

  let implied_consequences are_eq are_neq find env eqs la =
    let spl = env.split in
    let spl, eqs = SplitSet.fold (fun (ex, s) (spl, eqs) ->
      try (let ex, s, eqs1 = Split.fold (fun v (ex, s, eqs) ->
	match Conseq.simple are_eq are_neq env.terms env.rs v with
	  | Some (true, _) -> raise (No_cons eqs)
	  | Some (false, ex1) -> (Ex.union ex1 ex, s, eqs)
	  | None -> (ex, Split.add v s, eqs)) s
	     (ex, Split.empty, ESet.empty) in
	   if Split.is_empty s then raise (Unsat ex)
	   else
	     let eqs = ESet.union eqs eqs1 in
	     let v = Split.choose s in
	     if Split.is_empty (Split.remove v s) then
	       (spl, ESet.add (v, ex) eqs)
	     else SplitSet.add (ex, s) spl, eqs)
      with No_cons eqs1 -> (spl, ESet.union eqs eqs1)) 
      spl (SplitSet.empty, eqs) in
    {env with split = spl}, eqs

  let assume_one find are_eq are_neq class_of (env, assume) t =
    let res =
      match T.view t with
	| {T.f=Sy.Op Sy.Get; T.xs=[tst; te]; T.ty=ty} ->
	  (match (T.view tst).T.ty with
	    | Ty.Tfarray (ty1, Ty.Text ([ty2], hO)) ->
	      if ty1 = ty2 && Hstring.compare hO hOption = 0 then
		add_F find class_of are_eq are_neq (t, tst, te) env assume
	      else (env, assume)
	    | _ -> (env, assume))
	| {T.f=Sy.Op Sy.Set; T.xs=[tst; te; tk]} ->
	  (match (T.view tst).T.ty with
	    | Ty.Tfarray (ty1, Ty.Text ([ty2], hO)) ->
	      if ty1 = ty2 && Hstring.compare hO hOption = 0 then
		add_U find class_of are_eq are_neq (t, (tst, te, tk)) env assume
	      else (env, assume)
	    | _ -> (env, assume))
	| {T.f=Sy.Name (hr, Sy.Other); T.xs=[tst; te1; te2]; T.ty=Ty.Tbool} ->
	  if Hstring.compare hr hreach = 0 then
	    add_R find class_of are_eq are_neq t (tst, te1, te2) env assume
	  else (env, assume)
	| _ -> (env, assume) in
    res

  let review_uses find (env, assume) =
    let (env, use) = 
      T.Map.fold (update_env_st find) env.st_uses (env, USet.empty) in
    let (env, use) = T.Map.fold (update_env_e find) env.e_uses (env, use) in
    let assume, env = USet.fold (fun v (acc, env) ->
      match v with
	| GVal (tst, te) ->
	  let st, _ = T.Map.find tst env.terms in
	  let e, _ = T.Map.find te env.terms in
	  (match (Genv.find (st, e) env.gs) with
	    | GUnknown -> assert false
	    | GKnown v -> 
	      let acc,spl = f_add_conseq st e v env acc in
	      acc, {env with split=spl})
	| RVal (tst, te1, te2) ->
	  let st, _ = T.Map.find tst env.terms in
	  let e1, _ = T.Map.find te1 env.terms in
	  let e2, _ = T.Map.find te2 env.terms in
	  (match (Renv3.find e2 (Renv2.find (tst, te1) e1
				   (Renv.find st env.rs))) with
	    | RUnknown, _ -> (acc, env)
	    | RKnown v, _ ->
	      let acc,spl =
		r_add_conseq st e1 e2 v env acc in
	      acc, {env with split=spl})
	| UVal tst ->
	  let st2, _ = T.Map.find tst env.terms in
	  let v, _ = Uenv.find st2 env.us in
	  T.Map.fold (fun t (ex, (tst, te, tk)) (acc, env) ->
	    let st1, ex1 = T.Map.find tst env.terms in
	    let e, ex2 = T.Map.find te env.terms in
	    let ex = Ex.union (Ex.union ex1 ex2) ex in
	    let spl,acc = u_add_conseq (st2, st1, e) t (ex, (tst, te, tk))
	      env acc in
	    acc, {env with split=spl}) v (acc, env)
    ) use (assume, env) in
    (env, assume)

  let review_options find class_of are_eq are_neq (env, assume) =
    let env, assume = T.Map.fold (fun t (tst, te) (env, assume) ->
      add_F find class_of are_eq are_neq (t, tst, te) env assume)
      env.f_options ({env with f_options = T.Map.empty}, assume) in
    let env, assume = T.Map.fold (fun t (tst, te, tk) (env, assume) ->
      add_U find class_of are_eq are_neq (t, (tst, te, tk)) env assume)
      env.u_options ({env with u_options = T.Map.empty}, assume) in
    let env, assume = T.Map.fold (fun t (tst, te1, te2) (env, assume) ->
      add_R find class_of are_eq are_neq t (tst, te1, te2) env assume)
      env.r_options ({env with r_options = T.Map.empty}, assume) in
    env, assume

  let assume env la ~are_eq ~are_neq ~class_of ~find =
    let fct acc r =
      match X.term_extract r with
        | Some t -> 
          let {T.xs=xs} = T.view t in
          let res = List.fold_left (assume_one find are_eq are_neq class_of)
	    acc (t::xs) in res
        | None   -> acc
    in 
    try (
      let env, assume = (env, ESet.empty) in
      let env, assume = review_uses find (env, assume) in
      let env, assume = review_options find class_of are_eq are_neq 
	(env, assume) in
      let env, assume =
	List.fold_left (fun (env, assume) (a,t,ex) ->
	  match a with
	    | A.Eq (t1,t2) ->
	      let env, assume = fct (fct (env, assume) t1) t2 in
	      (env, assume)
	    | A.Builtin (_,_,l)
	    | A.Distinct (_, l) -> 
	      let env, assume = L.fold_left fct (env, assume) l in
	      (env, assume))
	  (env, assume) la in
      let assume = ESet.simple are_eq are_neq env.terms env.rs assume in
      let env, assume =
	implied_consequences are_eq are_neq find env assume la in
      Debug.env fmt env;
      Debug.new_equalities fmt assume;
      (env,
       { assume = ESet.fold (fun (a, e) acc ->
	 (LTerm (Conseq.make_t a), e)::acc) assume [];
	 remove = [] }))
    with Unsat e ->
      Debug.env fmt env;
      Debug.unsat fmt;
      (env, { assume = [LTerm A.LT.faux, e];
	      remove = [] } )

  let case_split env = 
    try
      (let ex, s = SplitSet.choose env.split in
      let v = Split.choose s in
      let a, exx = Conseq.make_s env.terms v in
      if debug_arrays then 
        fprintf fmt "[Arrays.case-split] %a@." LR.print a;
      [LR.view a, Ex.union ex exx, Num.Int (Split.cardinal s)])
    with Not_found ->
      if debug_arrays then fprintf fmt "[Arrays.case-split] Nothing@.";
      []
end
