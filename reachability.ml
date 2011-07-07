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

  let hReach = Hstring.make "reach"
  let hSome = Hstring.make "Some"
  let hNone = Hstring.make "None"
  let hOption = Hstring.make "option"
  let ty_option ty = Ty.Text ([ty], hOption)

  let rec find_val l =
    match l with
      | [] -> raise Not_found
      | t :: l -> 
	(match T.view t with
	  | {T.f=(Sy.Name (hh, Sy.Other)); T.xs=[e];
	    T.ty=ty} ->
	    if hh = hSome then Some e
	    else find_val l
	  | {T.f=(Sy.Name (hh, Sy.Other)); T.xs=[]} ->
	    if hh = hNone then None else find_val l
	  | _ -> find_val l)

  let make_some e =
    let ty = (T.view e).T.ty in
    T.make (Sy.Name (hSome, Sy.Other)) [e] (ty_option ty)

  let make_none e =
    let ty = (T.view e).T.ty in
    T.make (Sy.Name (hNone, Sy.Other)) [] (ty_option ty)

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
    let find e m = try find e m with Not_found -> (RUnknown, RUnknown)
    let add_v e v m = add e (merge_rvalue v (find e m)) m
    let remove_v e m = let _, v2 = find e m in
		       add e (RUnknown, v2) m
  end
  module Renv2 = struct
    include Map.Make(struct type t = X.r include X end)
    let find e m = try find e m with Not_found -> Renv3.empty
    let add_v e1 e2 v m = 
      let cluster1 = find e1 m in
      if e1 = e2 then
	add e1 (Renv3.add_v e1 (v, v) cluster1) m
      else
	let cluster2 = find e2 m in
	add e1 (Renv3.add_v e2 (v, RUnknown) cluster1)
	  (add e2 (Renv3.add_v e1 (RUnknown, v) cluster2) m)
    let remove_v e1 e2 m = 
      let cluster1 = find e1 m in
      let cluster2 = find e2 m in
      add e1 (Renv3.remove_v e2 cluster1)
	  (add e2 (Renv3.remove_v e1 cluster2) m)
  end
  module Renv = struct
    include Map.Make(struct type t = X.r include X end)
    let find st m = try find st m with Not_found -> Renv2.empty
    let add_v st e1 e2 v m =
      add st (Renv2.add_v e1 e2 v (find st m)) m
    let remove_v st e1 e2 m =
      add st (Renv2.remove_v e1 e2 (find st m)) m
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

  type split = SR of (T.t*T.t*T.t)
	       | SE of (T.t*T.t)
  module Split = struct
    type t = split
    let compare s1 s2 =
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
    let print fmt s =
      match s with
	| SR (r1, r2, r3) -> fprintf fmt "Reach (%a, %a, %a)@."
	  T.print r1 T.print r2 T.print r3
	| SE (r1, r2) -> fprintf fmt "%a = %a@."
	  T.print r1 T.print r2
  end

  (* Type for uses *)
  type use = GVal of (T.t*T.t) | RVal of (T.t*T.t*T.t)
	     | SVal of split
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
		 | SVal l1, SVal l2 -> Split.compare l1 l2
    end)
  end

  (* Type for consequences *)
  type conseq =
    | Split of (split * (conseq option) * (conseq option))
    | Lit of A.LT.t
  module ConseqMap = struct
    include Map.Make(Split)
    let find l m = try find l m with Not_found -> []
    let add l v m = add l (v :: find l m) m
  end

  (* Type for splits
     env.split maps ***positive*** occurences of literals to their
     representations *)
  module SplitSet = Set.Make(Split)
  module LRMap = struct
    include LR.Map
    let choose m =
      let x = ref (LR.make (A.Distinct (true, [])), true) in
      (try (iter (fun k _ -> x := k, false; raise Not_found) m)
       with Not_found -> ());
      if snd (!x) then raise Not_found
      else fst (!x)
    let find l m = try find l m with Not_found -> SplitSet.empty
    let add_v l s m =
      add l (SplitSet.add s (find l m)) m
  end

  let add_split split lr lcons splits conseqs uses =
    let uses =
      match split with
	| SR (tst, te1, te2) ->
	  let ust = T.Map.find tst uses in
	  let uses = T.Map.add tst (USet.add (SVal split) ust) uses in
	  let ue1 = T.Map.find te1 uses in
	  let uses = T.Map.add te1 (USet.add (SVal split) ue1) uses in
	  let ue2 = T.Map.find te2 uses in
	  T.Map.add te2 (USet.add (SVal split) ue2) uses
	| SE (te1, te2) ->
	  let ue1 = T.Map.find te1 uses in
	  let uses = T.Map.add te1 (USet.add (SVal split) ue1) uses in
	  let ue2 = T.Map.find te2 uses in
	  T.Map.add te2 (USet.add (SVal split) ue2) uses in
    let conseqs = List.fold_left
      (fun conseqs a -> ConseqMap.add split a conseqs) conseqs lcons in
    let splits = LRMap.add_v lr split splits in
    (splits, conseqs, uses)

  (* Type for the environment *)
  type t =
      {terms : X.r T.Map.t;
       uses : USet.t T.Map.t;
       gs : gvalue Genv.t;
       rs : (rvalue*rvalue) Renv3.t Renv2.t Renv.t;
       split : SplitSet.t LRMap.t;
       conseq : ((bool*conseq * Ex.t) list) ConseqMap.t}

  let empty _ =
    {terms = T.Map.empty;
     uses = T.Map.empty;
     gs = Genv.empty;
     rs = Renv.empty;
     split = LRMap.empty;
     conseq = ConseqMap.empty}

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

    let print_terms fmt = T.Map.iter
      (fun t r -> 
	    fprintf fmt "  %a -> %a@." T.print t X.print r)

    let print_used fmt = T.Map.iter
      (fun t v ->
	USet.iter
	  (fun v ->
	    match v with
	      | GVal (st, e) -> fprintf fmt "  %a -> G %a %a @." T.print t
		T.print st T.print e
	      | RVal (st, e1, e2) -> fprintf fmt "  %a -> R %a %a %a@."
		T.print t T.print st T.print e1 T.print e2
	      | SVal l -> fprintf fmt "  %a -> S %a@." T.print t 
		Split.print l) v)

    let print_splits fmt = 
      LRMap.iter (fun a _ -> fprintf fmt "%a@." LR.print a)

    let env fmt env = 
      if debug_arrays then begin
        fprintf fmt "-- reachs --------------------------------------@.";
        print_reachs fmt env.rs;
        fprintf fmt "-- gets ----------------------------------------@.";
        print_gets fmt env.gs;
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
          ESet.iter (fun (a,ex) ->
	    (*match a with
	    | Sem a -> fprintf fmt "  %a : %a@."
              LR.print a Ex.print ex
	    | Term a ->*) fprintf fmt "  %a : %a@."
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
		 | GVal (_, te) ->
		   let e = T.Map.find te terms in
		   let v = Genv.find (ost, e) env.gs in
		   if v = Genv.find (st, e) env.gs then
		     env, uset
		   else
		     let gs = Genv.add (st, e) (update_ex_f v ex) env.gs in
		     {env with gs=gs}, USet.add (GVal (tst, te)) uset
		 | _ -> failwith "not implemented") uses
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
			 {env with gs=gs}, USet.add (GVal (tst, te)) uset
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
		      let v, _ = Renv3.find oe (Renv2.find e1 
					       (Renv.find st env.rs)) in
		      let rs = Renv.remove_v st e1 oe env.rs in
		      let rs = Renv.add_v st e1 e (update_ex_r v ex) rs in
		      {env with rs=rs}, USet.add (RVal (tst, te1, te2)) uset)
		   else if te2 <> te then
		     (let e2 = T.Map.find te2 terms in
		      let v, _ = Renv3.find e2 (Renv2.find oe
					       (Renv.find st env.rs)) in
		      let rs = Renv.remove_v st oe e2 env.rs in
		      let rs = Renv.add_v st e e2 (update_ex_r v ex) rs in
		      {env with rs=rs}, USet.add (RVal (tst, te, te2)) uset)
		   else 
		     (let v, _ = Renv3.find oe (Renv2.find oe
					       (Renv.find st env.rs)) in
		      let rs = Renv.remove_v st oe oe env.rs in
		      let rs = Renv.add_v st e e (update_ex_r v ex) rs in
		      {env with rs=rs}, USet.add (RVal (tst, te, te)) uset)
		 | SVal (SR (tst, te1, te2)) ->
		   let st = T.Map.find tst terms in 
		   let ospl, spl =
		     if te1 <> te then
		       (let e1 = T.Map.find te1 terms in
			let ospl = make_sr (st, e1, oe) true in
			let spl = make_sr (st, e1, e) true in
			ospl, spl)
		     else if te2 <> te then
		       (let e2 = T.Map.find te2 terms in
			let ospl = make_sr (st, oe, e2) true in
			let spl = make_sr (st, e, e2) true in
			ospl, spl)
		     else
		       (let ospl = make_sr (st, oe, oe) true in
			let spl = make_sr (st, e, e) true in
			ospl, spl) in
		   let oe = LRMap.find ospl env.split in
		   let e = SplitSet.union oe (LRMap.find spl env.split) in
		   let split = LRMap.add spl e 
		     (LRMap.remove ospl env.split) in
		   {env with split=split}, uset
		 | SVal (SE (te1, te2)) ->
		   let ospl, spl =
		     if te1 <> te then
		       (let e1 = T.Map.find te1 terms in
			let ospl = LR.make (A.Eq (e1, oe)) in
			let spl = LR.make (A.Eq (e1, e)) in
			ospl, spl)
		     else if te2 <> te then
		       (let e2 = T.Map.find te2 terms in
			let ospl = LR.make (A.Eq (oe, e2)) in
			let spl = LR.make (A.Eq (e, e2)) in
			ospl, spl)
		     else
		       (let ospl = LR.make (A.Eq (oe, oe)) in
			let spl = LR.make (A.Eq (e, e)) in
			ospl, spl) in
		   let oe = LRMap.find ospl env.split in
		   let e = SplitSet.union oe (LRMap.find spl env.split) in
		   let split = LRMap.add spl e 
		     (LRMap.remove ospl env.split) in
		   {env with split=split}, uset
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
      acc splits conseqs uses =
    my_print_string "order";
    Renv3.fold (fun e3 (v, _) (splits, acc, conseqs, uses) ->
      match v with
	| RKnown (true, ex, (_, _, te3)) ->
	  let ex1 = Ex.union ex1 ex in
	  if e1 = e3 || e3 = e2 then
	    (splits, acc, conseqs, uses)
	  else
	    (my_print_string "+++ order";
	    let res1 = 
	      make_tr (tst, te2, te3) true in
	    let res2 = 
	      make_tr (tst, te3, te2) true in
	    match Renv3.find e3 r2 with
	      | RKnown (false, ex2, _), RKnown (false, ex3, _) ->
		raise (Unsat (Ex.union ex1 (Ex.union ex2 ex3)))
	      | RKnown (true, _, _), _
	      | _, RKnown (true, _, _) ->  splits, acc, conseqs, uses
	      | RKnown (false, ex2, _), RUnknown ->
		splits, ESet.add (res2, Ex.union ex1 ex2) acc,
		conseqs, uses
	      | RUnknown, RKnown (false, ex2, _) ->
		splits, ESet.add (res1, Ex.union ex1 ex2) acc,
		conseqs, uses
	      | RUnknown, RUnknown ->
		let split = SR (tst, te2, te3) in
		let lr = (make_sr (st, e2, e3) true) in
		let lcons = [(false, Lit res2, ex1); (true, Lit res1, ex1);
			     (false, Lit (A.LT.neg res1), ex1)] in
		let splits, conseqs, uses =
		  add_split split lr lcons splits conseqs uses in
		splits, acc, conseqs, uses)
	| _ -> (splits, acc, conseqs, uses)
    ) r1 (splits, acc, conseqs, uses)

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
      assume splits conseqs uses =
    my_print_string "reach2";
    (* e1 = e2 nothing to do *)
    if e1 = e2 then (splits, assume, conseqs, uses)
    else
      (my_print_string "+++ reach2";
      match res with
	(* k = None -> e1 = e2 *)
	| None ->
	  (match are_neq te1 te2 with
	    | Sig.No ->
	      let res = A.LT.make (A.Eq (te1, te2)) in
	      (splits, ESet.add (res, ex) assume, conseqs, uses)
	    | Sig.Yes exx -> raise (Unsat (Ex.union ex exx)))
	(* k = Some e3 *)
	| Some (e3, te3) ->
	  match snd (Renv3.find e3 r) with
	    | RKnown (true, _, _) ->
	      (* R(st, e3, e2) nothing to do *)
	      (splits, assume, conseqs, uses)
	    | RKnown (false, ex2, _) ->
	      (* not R(st, e3, e2) -> e1 = e2 *)
	      let ex = Ex.union ex ex2 in
	      (match are_neq te1 te2 with
		| Sig.No ->
		  let res = A.LT.make (A.Eq (te1, te2)) in
		  (splits, ESet.add (res, ex) assume, conseqs, uses)
		| Sig.Yes exx -> raise (Unsat (Ex.union ex exx)))
	    | RUnknown ->
	      let res = make_tr (tst, te3, te2) true in
	      (* R(st, e3, e2) or e1 = e2 *)
	      (match are_neq te1 te2 with
		| Sig.No ->
		  let eq = SE (te1, te2) in
		  let lcons = [(false, Lit res, ex)] in
		  let lr = (LR.make (A.Eq (e1, e2))) in
		  let splits, conseqs, uses =
		    add_split eq lr lcons splits conseqs uses in
		  (splits, assume, conseqs, uses)
		| Sig.Yes exx ->
		  (splits, ESet.add (res, Ex.union exx ex) assume,
		   conseqs, uses)))

  let rhandle_reach2 are_neq f r ex (st, e1, e2) (tst, te1, te2)
      assume splits conseqs uses =
    my_print_string "r reach2";
   match Genv.find (st, e1) f with
     | GUnknown -> (splits, assume, conseqs, uses)
     | GKnown (res, ex2, _) ->
       handle_reach2 are_neq r (Ex.union ex ex2) (st, e1, e2, res)
	 (tst, te1, te2) assume splits conseqs uses

  let fhandle_reach2 are_neq map r ex (st, e1, res) (tst, te1)
      assume splits conseqs uses =
    my_print_string "f reach2";
    Renv3.fold (fun e2 (v, _) (splits, assume, conseqs, uses) ->
      match v with
	| RKnown (true, ex1, (_, _, te2)) -> 
	  let r = Renv2.find e2 map in
	  handle_reach2 are_neq r (Ex.union ex ex1) (st, e1, e2, res)
	    (tst, te1, te2) assume splits conseqs uses
	| _ -> (splits, assume, conseqs, uses)) r
      (splits, assume, conseqs, uses)

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

    let r_add_conseq are_neq st e1 e2 (b, exp, term) env
	assume =
      let m = Renv.find st env.rs in
      let cluster1 = Renv2.find e1 m in
      let cluster2 = Renv2.find e2 m in
      let (_, v2) = Renv3.find e2 cluster1 in
      if b then
	if e1 = e2 then
	  assume, (env.split, env.conseq, env.uses)
	else
	  let assume = handle_antisym are_neq (e1, e2) term exp v2
	    assume in
	  let assume = handle_trans cluster1 cluster2 (e1, e2) term
	    exp assume in
	  let splits, assume, conseq, uses = handle_order cluster1 cluster2 
	    (st, e1, e2) term exp assume env.split env.conseq env.uses in
	  let splits, assume, conseq, uses = rhandle_reach2 are_neq
	    env.gs cluster2 exp (st, e1, e2) term assume splits conseq uses in
	  let assume = rhandle_wf are_neq env.gs exp (st, e1, e2) term assume in
	  assume, (splits, conseq, uses)
      else
	let assume = handle_refl are_neq (e1, e2) term exp assume in
	assume, (env.split, env.conseq, env.uses)

    let add_R are_neq st e1 e2 ((b, exp, (tst, te1, te2)) as v) env assume =
      let m = Renv.find st env.rs in
      let cluster1 = Renv2.find e1 m in
      let (v1, v2) = Renv3.find e2 cluster1 in
      match v1 with
	| RKnown (bb, ex, _) -> if b = bb then (env, assume)
	  else raise (Unsat (Ex.union exp ex))
	| RUnknown ->
	  let assume, (split, conseq, uses) =
	    r_add_conseq are_neq st e1 e2 v env assume in
	  let rs = Renv.add_v st e1 e2 (RKnown v) env.rs in
	  let ust = T.Map.find tst uses in
	  let uses = T.Map.add tst (USet.add (RVal (tst, te1, te2)) ust) uses in
	  let ue1 = T.Map.find te1 uses in
	  let uses = T.Map.add te1 (USet.add (RVal (tst, te1, te2)) ue1) uses in
	  let ue2 = T.Map.find te2 uses in
	  let uses = T.Map.add te2 (USet.add (RVal (tst, te1, te2)) ue2) uses in
	  {env with rs=rs; uses=uses; conseq=conseq; split=split}, assume

    let f_add_conseq are_neq st e (res, ex, (tst, te)) env
	assume =
      let map = Renv.find st env.rs in
      let r = Renv2.find e map in
      let assume =
	handle_reach1 r ex (st, e, res) (tst, te)
	  assume in
      let (splits, assume, conseq, uses) = 
	fhandle_reach2 are_neq map r ex (st, e, res) (tst, te)
	  assume env.split env.conseq env.uses in
      let assume = fhandle_wf are_neq r ex (st, e, res) assume in
      assume, (splits, conseq, uses)

    let add_F are_neq st e ((res, _, (tst, te)) as v) env assume =
      match Genv.find (st, e) env.gs with
	| GKnown _ -> (env, assume)
	| GUnknown ->
	  (* Todo : find another way to have this *)
	  let assume = if Renv3.mem e (Renv2.find e (Renv.find st env.rs)) then
	      assume
	    else ESet.add (make_tr (tst, te, te) true, Ex.empty)
	      assume in
	  let assume, (split, conseq, uses) = 
	    f_add_conseq are_neq st e v env assume in
	  let gs = Genv.add (st, e) (GKnown v) env.gs in
	  let v = GVal (tst, te) in
	  let ust, terms = try (T.Map.find tst uses, env.terms)
	    with Not_found -> USet.empty, T.Map.add tst st env.terms in
	  let uses = T.Map.add tst (USet.add v ust) uses in
	  let ue, terms = try (T.Map.find te uses, terms)
	    with Not_found -> USet.empty, T.Map.add te e terms in
	  let uses = T.Map.add te (USet.add v ue) uses in
	  let uses, terms = match res with
	    | None -> uses, terms
	    | Some (e, te) -> 
	      let ue, terms = try (T.Map.find te uses, terms)
		with Not_found -> USet.empty, T.Map.add te e terms in
	      T.Map.add te (USet.add v ue) uses, terms in
	  let env = {env with gs = gs; uses = uses; terms=terms;
	    split=split; conseq=conseq} in
	  (env, assume)

  let term_update are_neq find env (st, e1, e2) tst te1 te2
      acc =
    let env, st, use = update_env_st find env tst st USet.empty in
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
	      let acc,(spl,cons,uses) = f_add_conseq are_neq st e v env acc in
	      acc, {env with uses=uses; split=spl; conseq=cons})
	| RVal (tst, te1, te2) ->
	  let st = T.Map.find tst env.terms in
	  let e1 = T.Map.find te1 env.terms in
	  let e2 = T.Map.find te2 env.terms in
	  (match (Renv3.find e2 (Renv2.find e1 (Renv.find st env.rs))) with
	    | RUnknown, _ -> (acc, env)
	    | RKnown v, _ ->
	      let acc,(spl,cons,uses) =
		r_add_conseq are_neq st e1 e2 v env acc in
	      acc, {env with uses=uses; split=spl; conseq=cons})
	| _  -> acc, env) use (acc, env) in
    (env, (st, e1, e2), acc)

  let implied_consequences are_eq are_neq env eqs la =
    let rec h_conseq (spl, cons, acc) fact ex =
      match fact with
	| Lit l -> my_print_string "add_cons...\n";
	  (spl,cons, ESet.add (l, ex) acc)
	| Split (split, f1, f2) ->
	  let lr = match split with
	    | SR (t1, t2, t3) ->
	      let e1 = T.Map.find t1 env.terms in
	      let e2 = T.Map.find t2 env.terms in
	      let e3 = T.Map.find t3 env.terms in
	      make_sr (e1, e2, e3) true
	    | SE (t1, t2) ->
	      let e1 = T.Map.find t1 env.terms in
	      let e2 = T.Map.find t2 env.terms in
	      LR.make (A.Eq (e1, e2)) in
	  match f1, f2 with
	    | None, None -> assert false
	    | Some f1, None ->
	      let cons = ConseqMap.add split (true, f1, ex) cons in
	      (LRMap.add_v lr split spl, cons,acc)
	    | None, Some f2 ->
	      let cons = ConseqMap.add split (false, f2, ex) cons in
	      (LRMap.add_v lr split spl, cons,acc)
	    | Some f1, Some f2 ->
	      let cons = ConseqMap.add split (true, f1, ex) cons in
	      let cons = ConseqMap.add split (false, f2, ex) cons in
	      (LRMap.add_v lr split spl, cons,acc) in
    let spl, cons, eqs = 
      L.fold_left
        (fun (spl,cons,eqs) (a,_,e) ->
          let a = LR.make a in
	  let ltrue = LRMap.find a spl in
	  let lfalse = LRMap.find (LR.neg a) spl in
          let spl = LRMap.remove (LR.neg a) (LRMap.remove a spl) in
          let(spl,cons,eqs) =
	    SplitSet.fold
              (fun a acc -> 
		let (spl, cons, eq) = List.fold_left 
		(fun acc (b, fact, ex) ->
		  if b then h_conseq acc fact (Ex.union ex e)
		  else acc)
		acc (ConseqMap.find a cons) in
		let cons = ConseqMap.remove a cons in (spl, cons, eq)
	      ) ltrue (spl,cons,eqs) in
          let(spl,cons,eqs) =
	    SplitSet.fold
              (fun a acc ->
		let (spl, cons, eq) = List.fold_left 
		  (fun acc (b, fact, ex) -> 
		    if b then acc
		    else h_conseq acc fact (Ex.union ex e))
		  acc (ConseqMap.find a cons) in
		let cons = ConseqMap.remove a cons in (spl, cons, eq)
	      ) lfalse (spl,cons,eqs) in
          spl, cons, eqs
        )(env.split, env.conseq, eqs) la
    in
    let env = {env with split=spl; conseq=cons} in
    env, eqs

  let assume_one are_eq are_neq class_of
      (env, assume) t =
    let res =
    match T.view t with
      | {T.f=Sy.Op Sy.Get; T.xs=[tst; te]; T.ty=ty} ->
	(match (T.view tst).T.ty with
	  | Ty.Tfarray (ty1, Ty.Text ([ty2], hO)) ->
	    if ty1 = ty2 && hO = hOption then
	      let st, e = (fst(X.make(tst)), fst(X.make(te))) in
	      (try (
		let res = find_val (class_of t) in
		let ex, res = match res with
		  | None ->
		    (match are_eq t (make_none te) with
		      | Sig.No -> assert false
		      | Sig.Yes ex -> ex, None)
		  | Some e ->
		    (match are_eq t (make_some e) with
		      | Sig.No -> assert false
		      | Sig.Yes ex -> 
			ex, Some(fst(X.make e), e)) in
		add_F are_neq st e (res, ex, (tst, te)) env assume)
	      with Not_found -> (env, assume))
	    else (env, assume)
	  | _ -> (env, assume))
      | {T.f=Sy.Op Sy.Set; T.xs=[st; e; k]} ->
	(match (T.view st).T.ty with
	  | Ty.Tsum (hOption, [hSome; hNone]) ->
	    (env, assume) (* TODO *)
	  | _ -> (env, assume))
      | _ -> (env, assume) in
    res

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
      let env, assume =
	List.fold_left (fun (env, assume) (a,t,ex) ->
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
			(env, assume)
		      | _ -> assert false)
		  | None -> (env, assume))
	    | A.Eq (t1,t2) -> fct (fct (env, assume) t1) t2
	    | A.Builtin (_,_,l)
	    | A.Distinct (_, l) -> L.fold_left fct (env, assume) l)
	  (env, ESet.empty) la in
      let env, assume =
	implied_consequences are_eq are_neq env assume la in
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
      let a = LRMap.choose env.split in
      if debug_arrays then 
        fprintf fmt "[Arrays.case-split] %a@." LR.print a;
      [LR.view a, Ex.empty, Num.Int 2] 
    with Not_found ->
      if debug_arrays then fprintf fmt "[Arrays.case-split] Nothing@.";
      []
end
