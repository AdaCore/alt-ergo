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
  module X3Map = Map.Make(struct
    type t = X.r*X.r*X.r
    let compare (x11, x12, x13) (x21, x22, x23) =
      let c = X.compare x11 x21 in
      if c = 0 then
	let c = X.compare x12 x22 in
	if c = 0 then
	  X.compare x13 x23
	else c
      else  c end)

  let todo = false
  let my_print_string s = if todo then print_endline s

  let hReach = Hstring.make "reach"
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

  let make_tr (st, e1, e2) b =
    A.LT.make (A.Builtin (b, hReach, [st;e1;e2]))
  let make_sr (st, e1, e2) b =
    LR.make (A.Builtin (b, hReach, [st;e1;e2]))

  (* Type for equalities *)
  module ESet = Set.Make (struct 
    type t = (A.LT.t*Ex.t)
    let compare (t1, _) (t2, _) = A.LT.compare t1 t2 end)

  exception Unsat of Ex.t

  (* Type for reach *)
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

  (* Type for get *)
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

  (* Type for set *)
  type uvalue = Ex.t*(T.t*T.t*(X.r*T.t) option)

  let update_ex_u (e, t) ex =
    Ex.union e ex, t

  module Uenv = struct
    include Map.Make(struct type t = X.r include X end)
    let find e m = try find e m with Not_found -> T.Map.empty, T.Set.empty
  end

  (* Type for uses *)
  type use = GVal of (T.t*T.t) | RVal of (T.t*T.t*T.t)
	     (*| SVal of split*) | UVal of T.t
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

  (* Type for splits *)
  type split = SR of (T.t*T.t*T.t)
	       | SE of (T.t*T.t)
  module Split = struct
    include Set.Make (struct
      type t = bool * split
      let compare (b1, s1) (b2, s2) =
	if b1= b2 then
	  match s1, s2 with
	    | SR (r11, r12, r13), SR (r21, r22, r23) ->
	      let c = T.compare r11 r21 in
	      if c = 0 then
		let c = T.compare r12 r22 in
		if c = 0 then T.compare r13 r23 else c
	      else c
	    | SR _, _ -> -1
	    | _, SR _ -> 1
	    | SE (r11, r12), SE (r21, r22) ->
	      let c = T.compare r11 r21 in
	      if c = 0 then T.compare r12 r22 else c
	else if b1 then 1 else -1
    end)
    let print fmt (b, s) =
      if b then
	match s with
	  | SR (r1, r2, r3) -> fprintf fmt "reach (%a, %a, %a)"
	    T.print r1 T.print r2 T.print r3
	  | SE (r1, r2) -> fprintf fmt "%a = %a"
	    T.print r1 T.print r2
      else
	match s with
	  | SR (r1, r2, r3) -> fprintf fmt "~reach (%a, %a, %a)"
	    T.print r1 T.print r2 T.print r3
	  | SE (r1, r2) -> fprintf fmt "%a <> %a"
	    T.print r1 T.print r2 end

  module SplitSet =
    Set.Make (struct
      type t = Ex.t * Split.t
      let compare (_, s1) (_, s2) = Split.compare s1 s2 end)

  (* Type for the environment *)
  type t =
      {terms : X.r T.Map.t;
       uses : USet.t T.Map.t;
       gs : gvalue Genv.t;
       f_options : (T.t*T.t) T.Map.t;
       rs : (rvalue*rvalue) Renv3.t Renv2.t Renv.t;
       us : (uvalue T.Map.t*T.Set.t) Uenv.t;
       u_options : (T.t*T.t*T.t) T.Map.t;
       split : SplitSet.t}

  let empty _ =
    {terms = T.Map.empty;
     uses = T.Map.empty;
     gs = Genv.empty;
     f_options = T.Map.empty;
     rs = Renv.empty;
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
		| RKnown (b, _, (tst, te1, te2)) ->
		  fprintf fmt "%a [%a]@." LR.print
		    (make_sr (st, e1, e2) b) A.LT.print
		    (make_tr (tst, te1, te2) b) ))
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
      (fun t r -> 
	fprintf fmt "  %a -> %a@." T.print t X.print r)

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
	  (fun split -> fprintf fmt "%a " Split.print split)) s
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

    let env_on fmt env = 
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

    let new_equalities fmt st = 
      if debug_arrays then 
        begin
          fprintf fmt "[Reach] %d implied equalities@."
	    (ESet.cardinal st);
          ESet.iter (fun (a,ex) -> fprintf fmt "  %a : %a@."
            A.LT.print a Ex.print ex) st
        end

    let unsat fmt =
      if debug_arrays then 
        begin
          fprintf fmt "[Reach] 1 implied equalities@.";
          fprintf fmt "  false@."
        end
  end

  let update_env_st find env tst st uset =
    let terms = env.terms in
    try (let ost = T.Map.find tst terms in
	 if st = ost then env, st, uset
	 else
	   let st, ex = find tst in
	   if st = ost then env, st, uset
	   else
	     let env = {env with terms=T.Map.add tst st terms} in
	     let uses = T.Map.find tst env.uses in
	     let env, uset = USet.fold
	       (fun v (env, uset) -> match v with
		 | RVal (_, te1, te2) -> 
		   let e1 = T.Map.find te1 terms in
		   let e2 = T.Map.find te2 terms in
		   let v, _ = Renv3.find e1 (Renv2.find (tst, te2) e2
					       (Renv.find ost env.rs)) in
		   let rs = Renv.remove ost env.rs in
		   let rs = Renv.add_v (tst, te1, te2)
		     st e1 e2 (update_ex_r v ex) rs in
		   {env with rs=rs}, USet.add (RVal (tst, te1, te2)) uset
		 | GVal (_, te) ->
		   let e = T.Map.find te terms in
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
	     (env, st, uset))
    with Not_found ->
      let terms = T.Map.add tst st terms in
      let uses = T.Map.add tst USet.empty env.uses in
      {env with uses=uses; terms=terms}, st, USet.empty
	
  let update_env_e find env te e uset =
    let terms = env.terms in
    try (let oe = T.Map.find te terms in
	 if e = oe then env, e, uset
	 else
	   let e, ex = find te in
	   if e = oe then env, e, uset
	   else
	     let env = {env with terms=T.Map.add te e terms} in
	     let uses = T.Map.find te env.uses in
	     let env, uset = USet.fold
	       (fun v (env, uset) -> match v with
		 | GVal (tst, te1) ->
		   let st = T.Map.find tst terms in
		   if te <> te1 then
		     let e1 = T.Map.find te1 terms in
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
		   let st = T.Map.find tst terms in 
		   if te1 <> te then
		     (let e1 = T.Map.find te1 terms in
		      let v, _ = Renv3.find oe (Renv2.find (tst, te1) e1 
						  (Renv.find st env.rs)) in
		      let rs = Renv.remove_v (tst, te1, te2) st e1 oe env.rs in
		      let rs = Renv.add_v (tst, te1, te2)
			st e1 e (update_ex_r v ex) rs in
		      {env with rs=rs}, USet.add (RVal (tst, te1, te2)) uset)
		   else if te2 <> te then
		     (let e2 = T.Map.find te2 terms in
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
	     (env, e, uset))
    with Not_found ->
      let terms = T.Map.add te e terms in
      let uses = T.Map.add te USet.empty env.uses in
      {env with uses=uses; terms=terms}, e, USet.empty 

  (* REFLEXIVITY : If R(st, e1, e2)=false, assume e1 <> e2 *)
  let handle_refl are_neq (e1, e2) (_, te1, te2) ex assume =
    if e1 = e2 then raise (Unsat ex)
    else
      if are_neq te1 te2 <> Sig.No then assume
      else
	let diff = A.LT.make (A.Distinct (false, [te1; te2])) in
	(ESet.add (diff, ex) assume)

  (* ANTISYMMETRY : If R(st, e1, e2)=true and R(st, e2, e1)=true,
     assume e1 = e2 *)
  let handle_antisym are_neq (e1, e2) (_, te1, te2) ex1 v acc =
    my_print_string "antisym";
    match v with
      | RKnown (true, ex2, _) ->
	my_print_string "+++ antisym";
	if e1 = e2 then acc
	else
	  let exx = Ex.union ex1 ex2 in
	  (match are_neq te1 te2 with
	    | Sig.No -> 
	      ESet.add (A.LT.make (A.Eq (te1, te2)), exx) acc
	    | Sig.Yes ex -> raise (Unsat (Ex.union ex exx)))
      | _ -> acc 

  (* TRANSITIVITY : If R(st, e1, e2)=true, for all R(st, e3, e1)=true, assume
     R(st, e3, e2)=true, and, for all R(st, e2, e3)=true assume
     R(st, e1, e3)=rue *)
  let handle_trans r1 r2 (e1, e2) (tst, te1, te2) ex1 acc =
    my_print_string "trans";
    let acc = Renv3.fold (fun e3 (_, v) acc ->
      match v with
	| RKnown (true, ex2, (_, te3, _)) ->
	  if e1 = e3 || e3 = e2 then
	    acc
	  else
	    (my_print_string "+++ trans";
	     let ex = Ex.union ex1 ex2 in
	     let res = make_tr (tst, te3, te2) true in
	     match Renv3.find e3 r2 with
	       | _, RKnown (true, _, _) -> acc
	       | _, RKnown (false, ex3, _) -> raise (Unsat (Ex.union ex ex3))
	       | _ -> ESet.add (res, ex) acc)
	| _ -> acc) r1 acc in
    Renv3.fold (fun e3 (v, _) acc ->
      match v with
	| RKnown (true, ex2, (_, _, te3)) ->
	  if e1 = e3 || e3 = e2 then
	    acc
	  else
	    (my_print_string "+++ trans";
	     let ex = Ex.union ex1 ex2 in
	     let res = make_tr (tst, te1, te3) true in
	     match Renv3.find e3 r1 with
	       | RKnown (true, _, _), _ -> acc
	       | RKnown (false, ex3, _), _ -> raise (Unsat (Ex.union ex ex3))
	       | _ -> ESet.add (res, ex) acc)
	| _ -> acc) r2 acc

  (* ORDERING : If R(st, e1, e2)=true, for all R(st, e1, e3)=true, assume
     either R(st, e3, e2)=true or R(st, e2, e3)=true *)
  let handle_order r1 r2 (st, e1, e2) (tst, te1, te2) ex1
      acc splits =
    my_print_string "order";
    Renv3.fold (fun e3 (v, _) (splits, acc) ->
      match v with
	| RKnown (true, ex, (_, _, te3)) ->
	  let ex = Ex.union ex1 ex in
	  if e1 = e3 || e3 = e2 then
	    splits, acc
	  else
	    (my_print_string "+++ order";
	     let res1 = 
	       make_tr (tst, te2, te3) true in
	     let res2 = 
	       make_tr (tst, te3, te2) true in
	     match Renv3.find e3 r2 with
	       | RKnown (false, ex2, _), RKnown (false, ex3, _) ->
		 raise (Unsat (Ex.union ex (Ex.union ex2 ex3)))
	       | RKnown (true, _, _), _
	       | _, RKnown (true, _, _) ->  splits, acc
	       | RKnown (false, ex2, _), RUnknown ->
		 splits, ESet.add (res2, Ex.union ex ex2) acc
		 (*conseqs, uses*)
	       | RUnknown, RKnown (false, ex2, _) ->
		 splits, ESet.add (res1, Ex.union ex ex2) acc
		 (*conseqs, uses*)
	       | RUnknown, RUnknown ->
		 let res = Split.singleton (true, SR (tst, te2, te3)) in
		 let res = Split.add (true, SR (tst, te3, te2)) res in
		 let splits = SplitSet.add (ex, res) splits in
		 splits, acc)
	| _ -> splits, acc
    ) r1 (splits, acc)

  (* REACH1 : If st[e1] = Some e2, assume R(st, e1, e2)=true *)
  let handle_reach1 r ex (st, e, res) (tst, te)
      assume =
    my_print_string "reach1";
    match res with
      | None -> assume
      | Some (e2, te2) -> 
	(my_print_string "+++ reach1";
	 match fst(Renv3.find e2 r) with
	   | RKnown (true, _, _) -> assume
	   | RKnown (false, ex3, _) -> raise (Unsat (Ex.union ex ex3))
	   | RUnknown ->
	     let res = make_tr (tst, te, te2) true in
	     ESet.add (res, ex) assume)

  (* REACH2 : If R(st, e1, e2)=true and st[e1] = None, assume e1 = e2
     and if st[e1] = Some e3, assume either e1 = e2 or R(st, e3, e2)=true *)
  let handle_reach2 are_neq r ex (st, e1, e2, res) (tst, te1, te2)
      assume splits =
    my_print_string "reach2";
    (* e1 = e2 nothing to do *)
    if e1 = e2 then splits, assume
    else
      (my_print_string "+++ reach2";
       match res with
	 (* k = None -> e1 = e2 *)
	 | None ->
	   (match are_neq te1 te2 with
	     | Sig.No ->
	       let res = A.LT.make (A.Eq (te1, te2)) in
	       splits, ESet.add (res, ex) assume
	     | Sig.Yes exx -> raise (Unsat (Ex.union ex exx)))
	 (* k = Some e3 *)
	 | Some (e3, te3) ->
	   match snd (Renv3.find e3 r) with
	     | RKnown (true, _, _) ->
	       (* R(st, e3, e2) nothing to do *)
	       splits, assume
	     | RKnown (false, ex2, _) ->
	       (* not R(st, e3, e2) -> e1 = e2 *)
	       let ex = Ex.union ex ex2 in
	       (match are_neq te1 te2 with
		 | Sig.No ->
		   let res = A.LT.make (A.Eq (te1, te2)) in
		   splits, ESet.add (res, ex) assume
		 | Sig.Yes exx -> raise (Unsat (Ex.union ex exx)))
	     | RUnknown ->
	       let res = make_tr (tst, te3, te2) true in
	       (* R(st, e3, e2) or e1 = e2 *)
	       (match are_neq te1 te2 with
		 | Sig.No ->
		   let res = Split.singleton (true, SE (te1, te2)) in
		   let res = Split.add (true, SR (tst, te3, te2)) res in
		   let splits = SplitSet.add (ex, res) splits in
		   splits, assume
		 | Sig.Yes exx ->
		   splits, ESet.add (res, Ex.union exx ex) assume
	       ))

  let rhandle_reach2 are_neq f r ex (st, e1, e2) (tst, te1, te2)
      assume splits =
    my_print_string "r reach2";
    match Genv.find (st, e1) f with
      | GUnknown -> splits, assume
      | GKnown (res, ex2, _) ->
	handle_reach2 are_neq r (Ex.union ex ex2) (st, e1, e2, res)
	  (tst, te1, te2) assume splits

  let fhandle_reach2 are_neq map r ex (st, e1, res) (tst, te1)
      assume splits =
    my_print_string "f reach2";
    Renv3.fold (fun e2 (v, _) (splits, assume) ->
      match v with
	| RKnown (true, ex1, (_, _, te2)) -> 
	  let r = Renv2.find (tst, te2) e2 map in
	  handle_reach2 are_neq r (Ex.union ex ex1) (st, e1, e2, res)
	    (tst, te1, te2) assume splits
	| _ -> splits, assume) r
      (splits, assume)

  (* WELL-FOUNDED : If st[e1] = Some e3 and R(st, e2, e1)=true
     then assume e3 <> e2 *)
  let handle_wf are_neq ex (res, e2, te2) assume =
    my_print_string "wf";
    match res with
      | None -> assume
      | Some (e3, te3) ->
        my_print_string "++wf";
	if e3 = e2 then
	  raise (Unsat ex)
	else
	  if are_neq te3 te2 <> Sig.No then assume
	  else
	    let eq = A.LT.make (A.Distinct (false, [te3; te2])) in
	    (ESet.add (eq, ex) assume)
	      
  let rhandle_wf are_neq f ex (st, e1, e2) (_, te1, _) assume =
    my_print_string "r wf";
    match Genv.find (st, e2) f with
      | GUnknown -> assume
      | GKnown (res, ex2, _) ->
	handle_wf are_neq (Ex.union ex ex2) (res, e1, te1) assume

  let fhandle_wf are_neq r ex (st, e, res) assume =
    my_print_string "f wf";
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
		  handle_wf are_neq (Ex.union ex ex2) (res, e3, te3) acc
		| _ -> acc) r assume

  (* st[e1 <- Some (e2)] -> - R (st, e2, e1) *)
  let handle_wrong_update rs ex (st, e1, e2) (tst, te1, te2) assume =
    match fst(Renv3.find e1 (Renv2.find (tst, te2) e2 (Renv.find st rs))) with
      | RKnown (false, _, _) -> assume
      | RKnown (true, ex2, _) -> raise (Unsat (Ex.union ex ex2))
      | RUnknown -> let res = make_tr (tst, te2, te1) false in
		    ESet.add (res, ex) assume

  (* R (st[e1 <- Some (e2)], x1, x2) ->
     R (st, x1, e1) -> e1 = x2 \/ R (st, x1, x2)/\- R (st, e1, x2) \/
     R (st, e2, x2)
     - R (st, x1, e1) -> R (st, x1, x2) *)
  let handle_update_Some are_neq rs ex
      (tst, te1, te2, tx1, tx2) assume splits =
    let res1 = Split.singleton (true, SE (te1, tx2)) in
    let res1 = Split.add (true, SR (tst, te2, tx2)) res1 in
    let res1 = Split.add (false, SR (tst, tx1, te1)) res1 in
    let res2 = Split.add (false, SR (tst, te1, tx2)) res1 in
    let res1 = Split.add (true, SR (tst, tx1, tx2)) res1 in
    let res3 = Split.singleton (true, SR (tst, tx1, te1)) in
    let res3 = Split.add (true, SR (tst, tx1, tx2)) res3 in
    let splits = SplitSet.add (ex, res1) splits in
    let splits = SplitSet.add (ex, res2) splits in
    let splits = SplitSet.add (ex, res3) splits in
    splits, assume

  (* R (st[e <- None], x1, x2) ->
     R (st, x1, e) -> e = x2 \/ R (st, x1, x2)/\- R (st, e, x2)
     - R (st, x1, e) -> R (st, x1, x2) *)
  let handle_update_None are_neq rs ex
      (tst, te, tx1, tx2) assume splits =
    let res1 = Split.singleton (true, SE (te, tx2)) in
    let res1 = Split.add (false, SR (tst, tx1, te)) res1 in
    let res2 = Split.add (false, SR (tst, te, tx2)) res1 in
    let res1 = Split.add (true, SR (tst, tx1, tx2)) res1 in
    let res3 = Split.singleton (true, SR (tst, tx1, te)) in
    let res3 = Split.add (true, SR (tst, tx1, tx2)) res3 in
    let splits = SplitSet.add (ex, res1) splits in
    let splits = SplitSet.add (ex, res2) splits in
    let splits = SplitSet.add (ex, res3) splits in
    splits, assume

  let uhandle_update_Some are_neq rs ex st2
      (tst, te1, te2) assume splits =
    let m = Renv.find st2 rs in
    Renv2.fold (fun _ r acc -> Renv3.fold (fun _ (v, _)
      (splits, assume) ->
	match v with
	  | RKnown (true, ex1, (_, tx1, tx2)) ->
	    let ex = Ex.union ex ex1 in
	    handle_update_Some are_neq rs ex
	      (tst, te1, te2, tx1, tx2) assume splits
	  | _ -> splits, assume) r acc) m
      (splits, assume)

  let uhandle_update_None are_neq rs ex st2
      (tst, te) assume splits =
    let m = Renv.find st2 rs in
    Renv2.fold (fun _ r acc -> Renv3.fold (fun _ (v, _)
      (splits, assume) ->
	match v with
	  | RKnown (true, ex1, (_, tx1, tx2)) ->
	    let ex = Ex.union ex ex1 in
	    handle_update_None are_neq rs ex
	      (tst, te, tx1, tx2) assume splits
	  | _ -> splits, assume) r acc) m
      (splits, assume)

  let rhandle_update are_neq ts rs us ex (st, x1, x2)
      (_, tx1, tx2) assume splits =
    try (let v, _ = Uenv.find st us in 
	 T.Map.fold (fun _ (ex1, (tst, te1, tk))
	   (splits, assume) ->
	     let ex = Ex.union ex ex1 in
	     match tk with
	       | Some (_, te2) ->
		 handle_update_Some are_neq rs ex
		   (tst, te1, te2, tx1, tx2) assume splits
	       | None -> 
		 handle_update_None are_neq rs ex
		   (tst, te1, tx1, tx2) assume splits) v
	   (splits, assume))
    with Not_found -> assert false

  (* R (st, x1, x2), st[e <- k], - R (st, e, x2) -> R (st[e <- k], x1, x2) *)
  let uhandle_update_inv_1 m ex tst1 tst2 e te assume =
    let re = Renv2.find (tst1, te) e m in
    Renv3.fold (fun x2 (v, _) acc ->
      match v with
	| RKnown (false, ex1, (_, _, tx2)) ->
	  let rx2 = Renv2.find (tst1, tx2) x2 m in
	  let ex = Ex.union ex ex1 in
	  Renv3.fold (fun _ (_, v) acc ->
	    match v with
	      | RKnown (true, ex1, (_, tx1, _)) ->
		let ex = Ex.union ex ex1 in
		let res = make_tr (tst2, tx1, tx2) true in
		ESet.add (res, ex) acc
	      | _ -> acc) rx2 acc
	| _ -> acc) re assume

  (* R (st, x1, x2), st[e <- k], - R (st, x1, e) -> R (st[e <- k], x1, x2) *)
  let uhandle_update_inv_2 m ex tst1 tst2 e te assume =
    let re = Renv2.find (tst1, te) e m in
    Renv3.fold (fun x1 (_, v) acc ->
      match v with
	| RKnown (false, ex1, (_, tx1, _)) ->
	  let rx1 = Renv2.find (tst1, tx1) x1 m in
	  let ex = Ex.union ex ex1 in
	  Renv3.fold (fun _ (v, _) acc ->
	    match v with
	      | RKnown (true, ex1, (_, _, tx2)) ->
		let ex = Ex.union ex ex1 in
		let res = make_tr (tst2, tx1, tx2) true in
		ESet.add (res, ex) acc
	      | _ -> acc) rx1 acc
	| _ -> acc) re assume
    
  (* R (st, x, e), st[e <- k] -> R (st[e <- k], x, e) *)
  let uhandle_update_inv_3 m ex tst1 tst2 e te assume =
    let re = Renv2.find (tst1, te) e m in
    Renv3.fold (fun _ (_, v) acc ->
      match v with
	| RKnown (true, ex1, (_, tx, _)) ->
	  let ex = Ex.union ex ex1 in
	  let res = make_tr (tst2, tx, te) true in
	  ESet.add (res, ex) acc
	| _ -> acc) re assume

  (* R (st, x1, x2), R (st, e2, x2), st[e1 <- Some e2] ->
     R (st[e <- k], x1, x2) *)
  let uhandle_update_inv_4 m ex tst1 tst2 (e1, e2) (te1, te2) assume =
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
		let res = make_tr (tst2, tx1, tx2) true in
		ESet.add (res, ex) acc
	      | _ -> acc) rx2 acc
	| _ -> acc) re2 assume

  (* R (st, x1, e1), R (st, e2, x2), st[e <- Some e2] ->
     R (st[e <- k], x1, x2) *)
  let uhandle_update_inv_5 m ex tst1 tst2 (e1, e2) (te1, te2) assume =
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
		let res = make_tr (tst2, tx1, tx2) true in
		ESet.add (res, ex) acc
	      | _ -> acc) re1 acc
	| _ -> acc) re2 assume

  let uhandle_update_inv_Some rs ex tst1 tst2 (st, e1, e2)
      (te1, te2) assume =
    let m = Renv.find st rs in
    let assume = 
      uhandle_update_inv_4 m ex tst1 tst2 (e1, e2) (te1, te2) assume in
    let assume = 
      uhandle_update_inv_5 m ex tst1 tst2 (e1, e2) (te1, te2) assume in
    assume

  let uhandle_update_inv rs ex tst1 tst2 (st, e) te k assume =
    let m = Renv.find st rs in
    let assume = 
      uhandle_update_inv_1 m ex tst1 tst2 e te assume in
    let assume = 
      uhandle_update_inv_2 m ex tst1 tst2 e te assume in
    let assume = 
      uhandle_update_inv_3 m ex tst1 tst2 e te assume in
    assume

  (* R (st, x1, x2), st[e <- k], - R (st, e, x2) -> R (st[e <- k], x1, x2) *)
  let rhandle_update_inv_11 m ex tst1 tst2 (e, te) (x1, tx1) (x2, tx2) assume =
    let re = Renv2.find (tst1, te) e m in
    match fst (Renv3.find x2 re) with
      | RKnown (false, ex1, _) ->
	let ex = Ex.union ex ex1 in
	let res = make_tr (tst2, tx1, tx2) true in
	ESet.add (res, ex) assume
      | _ -> assume

  (* R (st, x1, x2), st[e <- k], - R (st, e, x2) -> R (st[e <- k], x1, x2) *)
  let rhandle_update_inv_12 m ex tst1 tst2 (e, _) (ee, _) (x2, tx2) assume =
    if e = ee then
      let rx2 = Renv2.find (tst1, tx2) x2 m in
      Renv3.fold (fun _ (_, v) acc ->
	match v with
	  | RKnown (true, ex1, (_, tx1, _)) ->
	    let ex = Ex.union ex ex1 in
	    let res = make_tr (tst2, tx1, tx2) true in
	    ESet.add (res, ex) acc
	  | _ -> acc) rx2 assume
    else assume

  (* R (st, x1, x2), st[e <- k], - R (st, x1, e) -> R (st[e <- k], x1, x2) *)
  let rhandle_update_inv_21 m ex tst1 tst2 (e, _) (x1, tx1) (x2, tx2) assume =
    let rx1 = Renv2.find (tst1, tx1) x1 m in
    match fst (Renv3.find e rx1) with
      | RKnown (false, ex1, _) ->
	let ex = Ex.union ex ex1 in
	let res = make_tr (tst2, tx1, tx2) true in
	ESet.add (res, ex) assume
      | _ -> assume

  (* R (st, x1, x2), st[e <- k], - R (st, x1, e) -> R (st[e <- k], x1, x2) *)
  let rhandle_update_inv_22 m ex tst1 tst2 (e, _) (x1, tx1) (ee, _) assume =
    if e = ee then
      let rx1 = Renv2.find (tst1, tx1) x1 m in
      Renv3.fold (fun _ (v, _) acc ->
	match v with
	  | RKnown (true, ex1, (_, _, tx2)) ->
	    let ex = Ex.union ex ex1 in
	    let res = make_tr (tst2, tx1, tx2) true in
	    ESet.add (res, ex) acc
	  | _ -> acc) rx1 assume
    else assume

  (* R (st, x, e), st[e <- k] -> R (st[e <- k], x, e) *)
  let rhandle_update_inv_3 m ex _ tst2 (e, _) (x, tx) (ee, te) assume =
    if e = ee then
      let res = make_tr (tst2, tx, te) true in
      ESet.add (res, ex) assume
    else assume

  (* R (st, x1, x2), R (st, e2, x2), st[e1 <- Some e2] ->
     R (st[e <- k], x1, x2) *)
  let rhandle_update_inv_41 m ex tst1 tst2 (_, _) (e2, te2) (x1, tx1) (x2, tx2)
      assume =
    let re2 = Renv2.find (tst1, te2) e2 m in
    match fst (Renv3.find x2 re2) with
      | RKnown (false, ex1, _) ->
	let ex = Ex.union ex ex1 in
	let res = make_tr (tst2, tx1, tx2) true in
	ESet.add (res, ex) assume
      | _ -> assume

  (* R (st, x1, x2), R (st, e2, x2), st[e1 <- Some e2] ->
     R (st[e <- k], x1, x2) *)
  let rhandle_update_inv_42 m ex tst1 tst2 (_, _) (e2, _) (ee2, _) (x2, tx2)
      assume =
    if e2 = ee2 then
      let rx2 = Renv2.find (tst1, tx2) x2 m in
      Renv3.fold (fun _ (_, v) acc ->
	match v with
	  | RKnown (true, ex1, (_, tx1, _)) ->
	    let ex = Ex.union ex ex1 in
	    let res = make_tr (tst2, tx1, tx2) true in
	    ESet.add (res, ex) acc
	  | _ -> acc) rx2 assume
    else assume

  (* R (st, x1, e1), R (st, e2, x2), st[e <- Some e2] ->
     R (st[e <- k], x1, x2) *)
  let rhandle_update_inv_51 m ex tst1 tst2 (e1, _) (e2, te2) (x1, tx1) (ee1, _)
      assume  =
    if e1 = ee1 then
      let re2 = Renv2.find (tst1, te2) e2 m in
      Renv3.fold (fun _ (v, _) acc ->
	match v with
	  | RKnown (true, ex1, (_, _, tx2)) ->
	    let ex = Ex.union ex ex1 in
	    let res = make_tr (tst2, tx1, tx2) true in
	    ESet.add (res, ex) acc
	  | _ -> acc) re2 assume
    else assume

  (* R (st, x1, e1), R (st, e2, x2), st[e <- Some e2] ->
     R (st[e <- k], x1, x2) *)
  let rhandle_update_inv_52 m ex tst1 tst2 (e1, te1) (e2, _) (ee2, _) (x2, tx2)
      assume  =
    if e2 = ee2 then
      let re1 = Renv2.find (tst1, te1) e1 m in
      Renv3.fold (fun _ (_, v) acc ->
	match v with
	  | RKnown (true, ex1, (_, tx1, _)) ->
	    let ex = Ex.union ex ex1 in
	    let res = make_tr (tst2, tx1, tx2) true in
	    ESet.add (res, ex) acc
	  | _ -> acc) re1 assume
    else assume

  let rhandle_update_inv_t rs us ts ex (st, x1, x2) (tst, tx1, tx2) assume =
    let m = Renv.find st rs in
    let _, s = Uenv.find st us in
    T.Set.fold (fun st2 acc ->
      let v, _ = Uenv.find (T.Map.find st2 ts) us in
      T.Map.fold (fun tst2 (ex1, (tst1, te, k)) acc ->
	if T.Map.find tst1 ts = st then
	  let ex = Ex.union ex ex1 in
	  let e = T.Map.find te ts in
	  let assume = rhandle_update_inv_11 m ex tst1 tst2 (e, te) (x1, tx1) 
	    (x2, tx2) assume in
	  let assume = rhandle_update_inv_21 m ex tst1 tst2 (e, te) (x1, tx1) 
	    (x2, tx2) assume in
	  let assume = rhandle_update_inv_3 m ex tst1 tst2 (e, te) (x1, tx1) 
	    (x2, tx2) assume in
	  match k with
	    | None -> assume
	    | Some (e2, te2) ->
	      let assume = rhandle_update_inv_41 m ex tst1 tst2 (e, te) 
		(e2, te2) (x1, tx1) (x2, tx2) assume in
	      let assume = rhandle_update_inv_42 m ex tst1 tst2 (e, te) 
		(e2, te2) (x1, tx1) (x2, tx2) assume in
	      let assume = rhandle_update_inv_51 m ex tst1 tst2 (e, te) 
		(e2, te2) (x1, tx1) (x2, tx2) assume in
	      let assume = rhandle_update_inv_52 m ex tst1 tst2 (e, te) 
		(e2, te2) (x1, tx1) (x2, tx2) assume in
	      assume
	else acc) v acc) s assume

  let rhandle_update_inv_f rs us ts ex (st, x1, x2) (tst, tx1, tx2) assume =
    let m = Renv.find st rs in
    let _, s = Uenv.find st us in
    T.Set.fold (fun st2 acc ->
      let v, _ = Uenv.find (T.Map.find st2 ts) us in
      T.Map.fold (fun tst2 (ex1, (tst1, te, _)) acc ->
	if T.Map.find tst1 ts = st then
	  let ex = Ex.union ex ex1 in
	  let e = T.Map.find te ts in
	  let assume = rhandle_update_inv_12 m ex tst1 tst2 (e, te) (x1, tx1) 
	    (x2, tx2) assume in
	  let assume = rhandle_update_inv_22 m ex tst1 tst2 (e, te) (x1, tx1) 
	    (x2, tx2) assume in
	  assume
	else acc) v acc) s assume

  let r_add_conseq are_neq st e1 e2 (b, exp, (tst, te1, te2 as term)) env
      assume =
    let m = Renv.find st env.rs in
    let cluster1 = Renv2.find (tst, te1) e1 m in
    let cluster2 = Renv2.find (tst, te2) e2 m in
    let (_, v2) = Renv3.find e2 cluster1 in
    if b then
      if e1 = e2 then
	assume, env.split
      else
	let assume = handle_antisym are_neq (e1, e2) term exp v2
	  assume in
	let assume = handle_trans cluster1 cluster2 (e1, e2) term
	  exp assume in
	let splits, assume = handle_order cluster1 cluster2 
	  (st, e1, e2) term exp assume env.split in
	let splits, assume = rhandle_reach2 are_neq
	  env.gs cluster2 exp (st, e1, e2) term assume splits in
	let assume = rhandle_wf are_neq env.gs exp (st, e1, e2) term assume in
	let splits, assume = rhandle_update are_neq env.terms
	  env.rs env.us exp (st, e1, e2) term assume splits in
	let assume = rhandle_update_inv_t env.rs env.us env.terms exp
	  (st, e1, e2) term assume in
	assume, splits
    else
      let assume = handle_refl are_neq (e1, e2) term exp assume in
      let assume = rhandle_update_inv_f env.rs env.us env.terms exp
	(st, e1, e2) term assume in
      assume, env.split

  let add_R are_neq st e1 e2 ((b, exp, (tst, te1, te2)) as v) env assume =
    try (let m = Renv.find st env.rs in
	 let cluster1 = Renv2.find (tst, te1) e1 m in
	 let (v1, v2) = Renv3.find e2 cluster1 in
	 match v1 with
	   | RKnown (bb, ex, _) -> if b = bb then (env, assume)
	     else raise (Unsat (Ex.union exp ex))
	   | RUnknown ->
	     let uses = env.uses in
	     let rs = Renv.add_v (tst, te1, te2) st e1 e2 (RKnown v) env.rs in
	     let ust = T.Map.find tst uses in
	     let uses = T.Map.add tst (USet.add (RVal (tst, te1, te2)) ust)
	       uses in
	     let ue1 = T.Map.find te1 uses in
	     let uses = T.Map.add te1 (USet.add (RVal (tst, te1, te2)) ue1)
	       uses in
	     let ue2 = T.Map.find te2 uses in
	     let uses = T.Map.add te2 (USet.add (RVal (tst, te1, te2)) ue2)
	       uses in
	     let env = {env with rs=rs; uses=uses} in
	     let assume, split =
	       r_add_conseq are_neq st e1 e2 v env assume in
	     {env with split=split}, assume)
    with Not_found -> assert false

  let f_add_conseq are_neq st e (res, ex, (tst, te)) env
      assume =
    let map = Renv.find st env.rs in
    let r = Renv2.find (tst, te) e map in
    let assume =
      handle_reach1 r ex (st, e, res) (tst, te)
	assume in
    let (splits, assume) = 
      fhandle_reach2 are_neq map r ex (st, e, res) (tst, te)
	assume env.split in
    let assume = fhandle_wf are_neq r ex (st, e, res) assume in
    assume, splits

  let add_F_val are_neq (res, ex, (tst, te)) env assume =
    let terms, uses = env.terms, env.uses in
    let v = GVal (tst, te) in
    let st, ust, terms = try (T.Map.find tst terms,
			      T.Map.find tst uses, terms)
      with Not_found -> let st = fst(X.make tst) in
			st, USet.empty, T.Map.add tst st terms in
    let uses = T.Map.add tst (USet.add v ust) uses in
    let e, ue, terms = try (T.Map.find te terms,
			    T.Map.find te uses, terms)
      with Not_found -> let e = fst(X.make te) in
			e, USet.empty, T.Map.add te e terms in
    let uses = T.Map.add te (USet.add v ue) uses in
    let res, uses, terms = match res with
      | None -> None, uses, terms
      | Some te -> 
	let e, uses, terms =
	  try (T.Map.find te terms,
	       T.Map.add te (USet.add v (T.Map.find te uses)) uses, terms)
	  with Not_found ->
	    let e = fst(X.make te) in
	    e, T.Map.add te (USet.singleton v) uses, T.Map.add te e terms in
	Some (e, te), uses, terms in
    match Genv.find (st, e) env.gs with
      | GKnown _ -> (env, assume)
      | GUnknown ->
	(* TODO : find another way to have this ? *)
	let assume = if Renv3.mem e (Renv2.find (tst, te) e 
				       (Renv.find st env.rs)) then assume
	  else ESet.add (make_tr (tst, te, te) true, Ex.empty)
	    assume in
	let v = (res, ex, (tst, te)) in
	let env = {env with terms=terms; uses=uses} in
	let assume, split = 
	  f_add_conseq are_neq st e v env assume in
	let gs = Genv.add (st, e) (GKnown v) env.gs in
	let env = {env with gs = gs; split=split} in
	(env, assume)

  let add_F class_of are_eq are_neq (t, tst, te) env assume =
    try (
      let tt, res = find_val (class_of t) in
      let ex = 
	match are_eq t tt with
	  | Sig.No -> assert false
	  | Sig.Yes ex -> ex in
      add_F_val are_neq (res, ex, (tst, te)) env assume)
    with Not_found ->
      ({env with f_options=T.Map.add t (tst, te) env.f_options}, assume)

  let u_add_conseq are_neq (st2, st1, e) t (ex, (tst, te, tk)) env assume =
    let splits = env.split in
    let assume = uhandle_update_inv env.rs ex tst t (st1, e) te tk assume in
    match tk with
      | None -> 
	uhandle_update_None are_neq env.rs ex st2 (tst, te) assume splits
      | Some (e2, te2) ->
	let assume =
	  handle_wrong_update env.rs ex (st1, e, e2) (tst, te, te2) assume
	in
	let splits, assume =
	  uhandle_update_Some are_neq env.rs ex st2
	    (tst, te, te2) assume splits in
	let assume = uhandle_update_inv_Some env.rs ex tst t (st1, e, e2) 
	  (te, te2) assume in
	splits, assume

  let add_U_val are_neq (t, ex, (tst, te, tk)) env assume =
    let terms, uses = env.terms, env.uses in
    let v = UVal t in
    let st2, ust, terms = try (T.Map.find t terms,
			       T.Map.find t uses, terms)
      with Not_found -> let st = fst(X.make t) in
			st, USet.empty, T.Map.add t st terms in
    let uses = T.Map.add t (USet.add v ust) uses in
    let st1, uses, terms = try (T.Map.find tst terms, uses, terms)
      with Not_found -> let st = fst(X.make tst) in
			st,T.Map.add tst USet.empty uses,
			T.Map.add tst st terms in
    let e, uses, terms = try (T.Map.find te terms, uses, terms)
      with Not_found -> let e = fst(X.make te) in
			e, T.Map.add te USet.empty uses,
			T.Map.add te e terms in
    let k, terms, uses = match tk with
      | None -> None, terms, uses
      | Some te -> 
	let e, terms, uses = try (T.Map.find te terms, terms, uses)
	  with Not_found -> let e = fst(X.make te) in
			    e, T.Map.add te e terms,
			    T.Map.add te USet.empty uses in
	Some (e, te), terms, uses in
    let uvals, uterms = Uenv.find st2 env.us in
    if T.Map.mem t uvals then (env, assume)
    else
      (* TODO : find another way to have this ? *)
      let assume = if Renv3.mem e (Renv2.find (t, te) e 
				     (Renv.find st2 env.rs)) then assume
	else ESet.add (make_tr (t, te, te) true, Ex.empty) assume in
      let v = (ex, (tst, te, k)) in
      let env = {env with terms = terms; uses = uses} in
      let split, assume = 
	u_add_conseq are_neq (st2, st1, e) t v env assume in
      let us = Uenv.add st2 (T.Map.add t v uvals, uterms)
	env.us in
      let us = Uenv.add st1 (match Uenv.find st1 us with
	| v, s -> v, T.Set.add t s) us in
      let env = {env with us = us; split=split} in
      (env, assume)

  let add_U class_of are_eq are_neq (t, (tst, te, tk)) env assume =
    try (
      let tt, res = find_val (class_of tk) in
      let ex =
	match are_eq tk tt with
	  | Sig.No -> assert false
	  | Sig.Yes ex -> ex in
      add_U_val are_neq (t, ex, (tst, te, res)) env assume)
    with Not_found ->
      ({env with u_options=T.Map.add t (tst, te, tk) env.u_options},
       assume)

  let term_update are_neq find env (st, e1, e2) tst te1 te2
      acc =
    try (let env, st, use = update_env_st find env tst st USet.empty in
	 let env, e1, use = update_env_e find env te1 e1 use in
	 let env, e2, use = update_env_e find env te2 e2 use in
	 let acc, env = USet.fold (fun v (acc, env) ->
	   match v with
	     | GVal (tst, te) ->
	       let st = T.Map.find tst env.terms in
	       let e = T.Map.find te env.terms in
	       (match (Genv.find (st, e) env.gs) with
		 | GUnknown -> assert false
		 | GKnown v -> 
		   let acc,spl = f_add_conseq are_neq st e v env
		     acc in
		   acc, {env with split=spl})
	     | RVal (tst, te1, te2) ->
	       let st = T.Map.find tst env.terms in
	       let e1 = T.Map.find te1 env.terms in
	       let e2 = T.Map.find te2 env.terms in
	       (match (Renv3.find e2 (Renv2.find (tst, te1) e1
					(Renv.find st env.rs))) with
		 | RUnknown, _ -> (acc, env)
		 | RKnown v, _ ->
		   let acc,spl =
		     r_add_conseq are_neq st e1 e2 v env acc in
		   acc, {env with split=spl})
	     | UVal tst ->
	       let st2 = T.Map.find tst env.terms in
	       let v, _ = Uenv.find st2 env.us in
	       T.Map.fold (fun t (ex, (tst, te, tk)) (acc, env) ->
		 let st1 = T.Map.find tst env.terms in
		 let e = T.Map.find te env.terms in
		 let spl,acc = u_add_conseq
		   are_neq (st2, st1, e) t (ex, (tst, te, tk)) env acc in
		 acc, {env with split=spl}) v (acc, env)
	 ) use (acc, env) in
	 (env, (st, e1, e2), acc))
    with Not_found -> assert false

  exception No_cons of (ESet.t)

  let implied_consequences are_eq are_neq find env eqs la =
    let spl = env.split in
    let spl, eqs = SplitSet.fold (fun (ex, s) (spl, eqs) ->
      try (let ex, s, eqs1 = Split.fold (fun (b, v) (ex, s, eqs) ->
	match v with
	  | SE (te1, te2) ->
	    let ex1, ex2 = if b then (are_eq te1 te2, are_neq te1 te2)
	      else (are_neq te1 te2, are_eq te1 te2) in
	    (match ex1, ex2 with
	      | Sig.Yes _, _ -> raise (No_cons eqs)
	      | _, Sig.Yes ex1 -> (Ex.union ex1 ex, s, eqs)
	      | _ -> (ex, Split.add (b, v) s, eqs))
	  | SR (tst, te1, te2) ->
	    let st, exst = find tst in
	    let e1, exe1 = find te1 in
	    let e2, exe2 = find te2 in
	    let w = Renv2.find (tst, te1) e1 (Renv.find st env.rs) in
	    match fst (Renv3.find e2 w) with
	      | RKnown (b1, ex1, _) -> 
		let ex = Ex.union (Ex.union ex (Ex.union exst ex1))
		  (Ex.union exe1 exe2) in
		if b1 = b then raise (No_cons eqs)
		else (Ex.union ex1 ex, s, eqs)
	      | RUnknown -> 
		try (
		  let b1, ex1 = X3Map.find (st, e1, e2) la in
		  let ex = Ex.union (Ex.union ex (Ex.union exst ex1))
		    (Ex.union exe1 exe2) in
		  let eqs = ESet.add (make_tr (tst, te1, te2) b1, ex) eqs in
		  if b = b1 then raise (No_cons eqs)
		  else (ex, s, eqs))
		with Not_found -> (ex, Split.add (b, v) s, eqs)) s
	     (ex, Split.empty, ESet.empty) in
	   if Split.is_empty s then raise (Unsat ex)
	   else
	     let eqs = ESet.union eqs eqs1 in
	     let (b, v) = Split.choose s in
	     if Split.is_empty (Split.remove (b, v) s) then
	       let e = match v with
		 | SE (te1, te2) -> A.LT.make (A.Eq (te1, te2))
		 | SR t -> make_tr t b in
	       (spl, ESet.add (e, ex) eqs)
	     else SplitSet.add (ex, s) spl, eqs)
      with No_cons eqs1 -> (spl, ESet.union eqs eqs1)) 
	    spl (SplitSet.empty, eqs) in
     {env with split = spl}, eqs

  let assume_one are_eq are_neq class_of
      (env, assume) t =
    let res =
      match T.view t with
	| {T.f=Sy.Op Sy.Get; T.xs=[tst; te]; T.ty=ty} ->
	  (match (T.view tst).T.ty with
	    | Ty.Tfarray (ty1, Ty.Text ([ty2], hO)) ->
	      if ty1 = ty2 && hO = hOption then
		add_F class_of are_eq are_neq (t, tst, te) env assume
	      else (env, assume)
	    | _ -> (env, assume))
	| {T.f=Sy.Op Sy.Set; T.xs=[tst; te; tk]} ->
	  (match (T.view tst).T.ty with
	    | Ty.Tfarray (ty1, Ty.Text ([ty2], hO)) ->
	      if ty1 = ty2 && hO = hOption then
		add_U class_of are_eq are_neq (t, (tst, te, tk)) env assume
	      else (env, assume)
	    | _ -> (env, assume))
	| _ -> (env, assume) in
    res

  let review_options class_of are_eq are_neq (env, assume) =
    let env, assume = T.Map.fold (fun t (tst, te) (env, assume) ->
      add_F class_of are_eq are_neq (t, tst, te) env assume)
      env.f_options ({env with f_options = T.Map.empty}, assume) in
    let env, assume = T.Map.fold (fun t (tst, te, tk) (env, assume) ->
      add_U class_of are_eq are_neq (t, (tst, te, tk)) env assume)
      env.u_options ({env with u_options = T.Map.empty}, assume) in
    env, assume

  let assume env la ~are_eq ~are_neq ~class_of ~find =
    let fct acc r =
      match X.term_extract r with
        | Some t -> 
          let {T.xs=xs} = T.view t in
          let res = List.fold_left (assume_one are_eq are_neq class_of)
	    acc (t::xs) in res

        | None   -> acc
    in 
    try (
      let env, assume = (env, ESet.empty) in
      let env, assume = review_options class_of are_eq are_neq (env, assume) in
      let env, assume, la =
	List.fold_left (fun (env, assume, la) (a,t,ex) ->
	  match a with
	    | A.Builtin (b, s, [st;e1;e2]) when Hstring.equal s hReach ->
	      let r = (st, e1, e2) in
	      (match t with
		| Some t -> 
		  (match A.LT.view t with
		    | A.Builtin (_, _, [tst;te1;te2]) ->
		      let env, r, assume =
			term_update are_neq find env r tst te1 te2 assume in
		      let (env, assume) = add_R are_neq st e1 e2 
			(b, ex, (tst, te1, te2)) env assume in
		      (env, assume, la)
		    | _ -> assert false)
		| None -> (env, assume, X3Map.add (st, e1, e2) (b, ex) la))
	    | A.Eq (t1,t2) ->
	      let env, assume = fct (fct (env, assume) t1) t2 in
	      (env, assume, la)
	    | A.Builtin (_,_,l)
	    | A.Distinct (_, l) -> 
	      let env, assume = L.fold_left fct (env, assume) l in
	      (env, assume, la))
	  (env, assume, X3Map.empty) la in
      let env, assume =
	implied_consequences are_eq are_neq find env assume la in
      Debug.env fmt env;
      Debug.new_equalities fmt assume;
      (env,
       { assume = ESet.fold (fun (a, e) acc ->
	 (LTerm a, e)::acc) assume [];
	 remove = [] }))
    with Unsat e ->
      Debug.env fmt env;
      Debug.unsat fmt;
      (env, { assume = [LTerm A.LT.faux, e];
	      remove = [] } )

  let case_split env = 
    try
      let ex, s = SplitSet.choose env.split in
      let b, a = Split.choose s in
      let a = match a with
	| SE (te1, te2) ->
	  let e1 = T.Map.find te1 env.terms in
	  let e2 = T.Map.find te1 env.terms in
	  if b then LR.make (A.Eq (e1, e2))
	  else LR.make (A.Distinct (false, [e1; e2]))
	| SR (tst, te1, te2) ->
	  let st = T.Map.find tst env.terms in
	  let e1 = T.Map.find te1 env.terms in
	  let e2 = T.Map.find te2 env.terms in
	  make_sr (st, e1, e2) b in
      if debug_arrays then 
        fprintf fmt "[Arrays.case-split] %a@." LR.print a;
      [LR.view a, ex, Num.Int (Split.cardinal s)] 
    with Not_found ->
      if debug_arrays then fprintf fmt "[Arrays.case-split] Nothing@.";
      []
end
