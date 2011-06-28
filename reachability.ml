open Options
open Format
open Sig

module Sy = Symbols
module T  = Term
module A  = Literal
module L  = List

module Make(X : Sig.X) = struct
  module Ex = Explanation

  type r = X.r

  let todo = false
  let my_print_string s = if todo then print_string s

  let hReach = Hstring.make "reach"
  let hSome = Hstring.make "Some"
  let hNone = Hstring.make "None"
  let hOption = Hstring.make "option"
  let ty_option ty = Ty.Text ([ty], hOption)
    (*Ty.Tsum (hOption, [hSome; hNone])*)

  module LR = Literal.Make(struct type t = X.r include X end)
  module TSet = Set.Make(struct type t = X.r include X end)
  module TMap = Map.Make(struct type t = X.r*X.r
				let compare (t11,t12) (t21, t22) =
				  let c = X.compare t11 t21 in
				  if c = 0 then X.compare t12 t22
				  else c
  end)
  module LRset = LR.Set
  module LRmap = struct
    include LR.Map
    let find l m = try find l m with Not_found -> []
    let add l v m = add l (v :: find l m) m
  end

  type result = Known of (bool*Ex.t)
		| Unknown

  type rtype = {rst : X.r; re1 : X.r; re2 : X.r}

  module R = struct
    include Map.Make(struct type t = X.r include X end)
    let find e m = try find e m with Not_found -> (Unknown, Unknown)
  end
  module RR = struct
    include Map.Make(struct type t = X.r include X end)
    let find e m = try find e m with Not_found -> R.empty
  end
  module RMap = struct
    include Map.Make(struct type t = X.r include X end)
    let find st m = try find st m with Not_found -> RR.empty
  end

  type gtype = {g:X.r; gt:X.r; gi:X.r}
      
  module ESet = Set.Make (struct 
    type t = (LR.t*Ex.t)
    let compare (t1, _) (t2, _) = LR.compare t1 t2 end)

  let add_rs {rst=st; re1=e1; re2=e2} (r1, r2) m =
    let tmap = RMap.find st m in
    let tmap = RR.add e1 (R.add e2 (r1, r2) (RR.find e1 tmap)) tmap in
    let tmap = RR.add e2 (R.add e1 (r2, r1) (RR.find e2 tmap)) tmap in
    RMap.add st tmap m

  type conseq =
    | Split of (T.t * T.t * (conseq option) * (conseq option))
    | Lit of (LR.t)

  type t =
      {gs : (X.r*X.r option*Ex.t) TMap.t;
       rs : (((result*result) R.t) RR.t) RMap.t;
       split : LRset.t;
       conseq : ((conseq * Ex.t) list) LRmap.t}

  let empty _ =
    {gs = TMap.empty;
     rs = RMap.empty;
     split = LRset.empty;
     conseq = LRmap.empty}

  exception Unsat of Ex.t

  let make_r st e1 e2 b =
    LR.make (A.Builtin (b, hReach, [st;e1;e2]))

  let rec find_val l =
    match l with
      | [] -> raise Not_found
      | t :: l -> 
	(match T.view t with
	  | {T.f=(Sy.Name (hh, Sy.Other(*Constructor*))); T.xs=[e];
	    T.ty=ty} ->
	    if hh = hSome then Some e
	    else find_val l
	  | {T.f=(Sy.Name (hh, Sy.Other(*Constructor*))); T.xs=[]} ->
	    if hh = hNone then None else find_val l
	  | _ -> find_val l)

  let make_some e =
    let ty = (T.view e).T.ty in
    T.make (Sy.Name (hSome, Sy.Other(*Constructor*))) [e] (ty_option ty)

  let make_none e =
    let ty = (T.view e).T.ty in
    T.make (Sy.Name (hNone, Sy.Other(*Constructor*))) [] (ty_option ty)

  module Debug = struct

    let assume fmt la = 
      if debug_arrays && la <> [] then begin
        fprintf fmt "++++++[Reach] We assume@.";
        L.iter (fun (a,_,_) -> fprintf fmt "  > %a@." 
          LR.print (LR.make a)) la;
      end

    let print_reachs fmt = RMap.iter 
      (fun st rr ->
	RR.iter (fun e1 r ->
	  R.iter (fun e2 k ->
	    match fst(k) with
	      | Unknown -> ()
	      | Known (true, _) ->
		fprintf fmt "%a@." LR.print (make_r st e1 e2 true)
	      | Known (false, _) -> 
		fprintf fmt "%a@." LR.print (make_r st e1 e2 false))
	    r) rr)
    let print_splits fmt = 
      LRset.iter (fun a -> fprintf fmt "%a@." LR.print a)

    let env fmt env = 
      if debug_arrays then begin
        fprintf fmt "-- reachs --------------------------------------@.";
        print_reachs fmt env.rs;
        fprintf fmt "-- reach splits --------------------------------@.";
        print_splits fmt env.split;
        fprintf fmt "------------------------------------------------@."
      end

    let new_equalities fmt st = 
      if debug_arrays then 
        begin
          fprintf fmt "[Reach] %d implied equalities@."
	    (ESet.cardinal st);
          ESet.iter (fun (a,ex) -> fprintf fmt "  %a : %a@."
            LR.print a Ex.print ex) st
        end
  end
    
  (* REFLEXIVITY : If R(st, e1, e2)=false, assume e1 <> e2 *)
  let handle_refl {rst=st; re1=e1; re2=e2} ex assume =
    if e1 = e2 then raise (Unsat ex)
    else
      let diff = LR.make (A.Distinct (false, [e1; e2])) in
      (ESet.add (diff, ex) assume)

  (* ANTISYMMETRY : If R(st, e1, e2)=true and R(st, e2, e1)=true,
     assume e1 = e2 *)
  let handle_antisym {re1=e1; re2=e2} ex1 v acc =
    my_print_string "antisym\n";
    match v with
      | Known (true, ex2) ->
	if e1 = e2 then acc
	else
	  ESet.add (LR.make (A.Eq (e1, e2)), Ex.union ex1 ex2) acc
      | _ -> acc 

  (* TRANSITIVITY : If R(st, e1, e2)=true, for all R(st, e3, e1)=true, assume
     R(st, e3, e2)=true, and, for all R(st, e2, e3)=true assume
     R(st, e1, e3)=rue *)
  let handle_trans r1 r2 {rst=st; re1=e1; re2=e2} ex1 acc =
    my_print_string "trans\n";
    let acc = R.fold (fun e3 (_, v) acc ->
      match v with
	| Known (true, ex2) ->
	  if e1 = e3 || e3 = e2 then
	    acc
	  else
	    (my_print_string "+++ trans\n";
	    let ex = Ex.union ex1 ex2 in
	    let res = make_r st e3 e2 true in
	    match R.find e3 r2 with
	      | _, Known (true, _) -> acc
	      | _, Known (false, ex3) -> raise (Unsat (Ex.union ex ex3))
	      | _ -> ESet.add (res, ex) acc)
	| _ -> acc) r1 acc in
    R.fold (fun e3 (v, _) acc ->
      match v with
	| Known (true, ex2) ->
	  if e1 = e3 || e3 = e2 then
	    acc
	  else
	    (my_print_string "+++ trans\n";
	    let ex = Ex.union ex1 ex2 in
	    let res = make_r st e1 e3 true in
	    match R.find e3 r1 with
	      | Known (true, _), _ -> acc
	      | Known (false, ex3), _ -> raise (Unsat (Ex.union ex ex3))
	      | _ -> ESet.add (res, ex) acc)
	| _ -> acc) r2 acc

  (* ORDERING : If R(st, e1, e2)=true, for all R(st, e1, e3)=true, assume
     either R(st, e3, e2)=true or R(st, e2, e3)=true *)
  let handle_order r1 r2 {rst=st; re1=e1; re2=e2} ex1
      acc splits conseqs =
    my_print_string "order\n";
    R.fold (fun e3 (v, _) (splits, acc, conseqs) ->
      match v with
	| Known (true, ex) ->
	  let ex1 = Ex.union ex1 ex in
	  if e1 = e3 || e3 = e2 then
	    (splits, acc, conseqs)
	  else
	    (my_print_string "+++ order\n";
	    let res1 = 
	      make_r st e2 e3 true in
	    let res2 = 
	      make_r st e3 e2 true in
	    match R.find e3 r2 with
	      | Known (false, ex2), Known (false, ex3) ->
		raise (Unsat (Ex.union ex1 (Ex.union ex2 ex3)))
	      | Known (true, _), _
	      | _, Known (true, _) ->  splits, acc, conseqs
	      | Known (false, ex2), Unknown ->
		splits, ESet.add (res2, Ex.union ex1 ex2) acc, conseqs
	      | Unknown, Known (false, ex2) ->
		splits, ESet.add (res1, Ex.union ex1 ex2) acc, conseqs
	      | Unknown, Unknown ->
		let conseqs = LRmap.add (LR.neg res1) (Lit res2, ex1)
		  conseqs in
		LRset.add res1 splits, acc, conseqs)
	| _ -> (splits, acc, conseqs)
    ) r1 (splits, acc, conseqs)

  (* REACH1 : If st[e1] = Some e2, assume R(st, e1, e2)=true *)
  let handle_reach1 r res ex {g=k; gt=st; gi=e}
      assume splits conseqs =
    my_print_string "reach1\n";
    match res with
      | None -> (splits, assume, conseqs)
      | Some e2 -> 
	(my_print_string "+++ reach1\n";
	match fst(R.find e2 r) with
	  | Known (true, _) -> (splits, assume, conseqs)
	  | Known (false, ex3) -> raise (Unsat (Ex.union ex ex3))
	  | Unknown ->
	    let res : LR.t = make_r st e e2 true in
	    (splits, ESet.add (res, ex) assume, conseqs))

  (* REACH2 : If R(st, e1, e2)=true and st[e1] = None, assume e1 = e2
     and if st[e1] = Some e3, assume either e1 = e2 or R(st, e3, e2)=true *)
  let handle_reach2 r res k e1 e2 st ex assume splits
      conseqs =
    my_print_string "reach2\n";
    (* e1 = e2 nothing to do *)
    if e1 = e2 then (splits, assume, conseqs)
    else
      (my_print_string "+++ reach2\n";
      match res with
	(* k = None -> e1 = e2 *)
	| None -> 
	  let res = LR.make (A.Eq (e1, e2)) in
	  (splits, ESet.add (res, ex) assume, conseqs)
	(* k = Some e3 *)
	| Some e3 ->
	  match snd (R.find e3 r) with
	    | Known (true, _) ->
	      (* R(st, e3, e2) nothing to do *)
	      (splits, assume, conseqs)
	    | Known (false, ex2) ->
	      (* not R(st, e3, e2) -> e1 = e2 *)
	      let res = LR.make (A.Eq (e1, e2)) in
	      let ex = Ex.union ex ex2 in
	      (splits, ESet.add (res, ex) assume, conseqs)
	    | Unknown ->
	      (* R(st, e3, e2) or e1 = e2 *)
	      let res = make_r st e3 e2 true in
	      let eq = LR.make (A.Eq (e1, e2)) in
	      let conseqs = LRmap.add (LR.neg eq) (Lit res, ex)
		conseqs in
	      (LRset.add eq splits, assume, conseqs))

  let rhandle_reach2 f r {rst=st; re1=e1; re2=e2} ex
      assume splits conseqs =
    my_print_string "r reach2\n";
    try (let k, res, ex2 = TMap.find (st, e1) f in
	 handle_reach2 r res k e1 e2 st (Ex.union ex ex2)
	   assume splits conseqs)
    with Not_found -> (splits, assume, conseqs)

  let fhandle_reach2 map r res ex {g=k; gt=st; gi=e}
      assume splits conseqs =
    my_print_string "f reach2\n";
    R.fold (fun e2 (v, _) (splits, assume, conseqs) ->
      match v with
	| Known (true, ex1) -> 
	  let r = RR.find e2 map in
	  handle_reach2 r res k e e2 st (Ex.union ex ex1)
	    assume splits conseqs
	| _ -> (splits, assume, conseqs)) r (splits, assume, conseqs)

  (* WELL-FOUNDED : If st[e] = Some e3 and R(st, e2, e)=true
     then assume e3 <> e2 *)
  let handle_wf res e2 ex assume =
    my_print_string "wf\n";
    match res with
      | None -> assume
      | Some e3 ->
        my_print_string "++wf\n";
	if e3 = e2 then
	  raise (Unsat ex)
	else 
	  let eq = LR.neg (LR.make (A.Eq (e3, e2))) in
	  (ESet.add (eq, ex) assume)
	
  let rhandle_wf f {rst=st; re1=e1; re2=e2} ex assume =
    my_print_string "r wf\n";
    try (let k, res, ex2 = TMap.find (st, e2) f in
	 handle_wf res e1 (Ex.union ex ex2) assume)
    with Not_found ->  assume 

  let fhandle_wf r res ex {g=k; gt=st; gi=e} assume =
    my_print_string "f wf\n";
    match res with
      | None -> assume
      | Some e2 ->
	match snd(R.find e2 r) with
	  | Known (true, ex2) -> 
	    raise (Unsat (Ex.union ex ex2))
	  | Known (false, _) -> assume
	  | Unknown ->
	    R.fold (fun e3 (_, v) acc ->
	      match v with
		| Known (true, ex2) ->
		  handle_wf res e3 (Ex.union ex ex2) acc
		| _ -> acc) r assume

  (* add_R assumes that R(st, e1, e2) = b (true or false) *)
  let add_R env ({rst=st; re1=e1; re2=e2} as r) exp
      b (splits, assume, conseq) =
    let map =  RMap.find st (env.rs) in
    let cluster1 = RR.find e1 map in
    let cluster2 = RR.find e2 map in
    let (v1, v2) = R.find e2 cluster1 in
    match v1 with
      | Known (b_old, ex) -> if b=b_old then (env, splits, assume, conseq)
	else raise (Unsat (Ex.union ex exp))
      | Unknown ->
	let splits, assume, conseq = if b then
	    if e1 = e2 then
	      (splits, assume, conseq)
	    else
	      let assume = handle_antisym r exp v2 assume in
	      let assume = handle_trans cluster1 cluster2 r exp assume in
	      let splits, assume, conseq = handle_order cluster1 cluster2 
		r exp assume splits conseq in
	      let splits, assume, conseq = rhandle_reach2 env.gs cluster2
		r exp assume splits conseq in
	      let assume = rhandle_wf env.gs r exp assume in
	      (splits, assume, conseq)
	  else
	    let assume = handle_refl r exp
	      assume in
	    splits, assume, conseq
	in
	let env = {env with rs = add_rs r (Known (b, exp), v2) env.rs} in
	(env, splits, assume, conseq)

  (* add_F assumes that f(st, e) = res (None or Some e') *)
  let add_F env res ex ({g=k; gt=st; gi=e} as f)
      (splits, assume, conseq) =
    try (ignore (TMap.find (st, e) env.gs); 
	 (env, splits, assume, conseq))
    with Not_found ->
      let map = RMap.find st env.rs in
      let r : (result * result) R.t = RR.find e map in
      let (splits, assume, conseq) =
	handle_reach1 r res ex f assume splits conseq in
      let (splits, assume, conseq) = 
	fhandle_reach2 map r res ex f
	  assume splits conseq in
      let assume = fhandle_wf r res ex f assume in
      let env = {env with gs = TMap.add (st, e) (k, res, ex) env.gs} in
      (env, splits, assume, conseq)

  let assume_one are_eq are_neq class_of
      (env, splits, assume, conseq) t =
    let res =
    match T.view t with
      | {T.f=Sy.Op Sy.Get; T.xs=[st; e]; T.ty=ty} ->
	(match (T.view st).T.ty with
	  | Ty.Tfarray (ty1, Ty.Text ([ty2], hO)) ->
	    if ty1 = ty2 && hO = hOption then
	      let f = {g = fst(X.make(t)); gt = fst(X.make(st));
		       gi = fst(X.make(e))} in
	      (try (
		let res = find_val (class_of t) in
		let ex, res = match res with
		  | None ->
		    (match are_eq t (make_none e) with
		      | Sig.No -> assert false
		      | Sig.Yes ex -> ex, None)
		  | Some e ->
		    (match are_eq t (make_some e) with
		      | Sig.No -> assert false
		      | Sig.Yes ex -> ex, Some(fst(X.make e))) in
		add_F env res ex f (splits, assume, conseq))
	      with Not_found -> (env, splits, assume, conseq))
	    else (env, splits, assume, conseq)
	  | _ -> (env, splits, assume, conseq))
      | {T.f=Sy.Op Sy.Set; T.xs=[st; e; k]} ->
	(match (T.view st).T.ty with
	  | Ty.Tsum (hOption, [hSome; hNone]) ->
	    (env, splits, assume, conseq) (* TODO *)
	  | _ -> (env, splits, assume, conseq))
      | _ -> (env, splits, assume, conseq) in
    res

  let case_split env = 
    try
      let a = LRset.choose env.split in
      [LR.view a, Ex.empty, Num.Int 2] 
    with Not_found ->
      if debug_arrays then fprintf fmt "[Arrays.case-split] Nothing@.";
      []

  let implied_consequences are_eq are_neq env eqs la =
    let rec h_conseq (spl, cons, acc) fact ex =
      match fact with
	| Lit l -> (spl,cons, ESet.add (l, ex) acc)
	| Split (t1, t2, f1, f2) ->
	  match are_eq t1 t2, are_neq t1 t2 with
	    | Sig.Yes _, Sig.Yes _ -> assert false
	    | Sig.Yes ex2, Sig.No ->
	      let ex = Ex.union ex ex2 in
	      (match f1 with
		| None -> (spl,cons,acc)
		| Some f1 -> h_conseq (spl, cons, acc) f1 ex)
	    | Sig.No, Sig.Yes ex2 ->
	      let ex = Ex.union ex ex2 in
	      (match f2 with
		| None -> (spl,cons,acc)
		| Some f2 -> h_conseq (spl, cons, acc) f2 ex)
	    | Sig.No, Sig.No ->
	      let split = LR.make(A.Eq(fst(X.make t1),
				       fst(X.make t2))) in
	    match f1, f2 with
	      | None, None -> assert false
	      | Some f1, None ->
		let cons = LRmap.add split (f1, ex) cons in
		(LRset.add split spl, cons,acc)
	      | None, Some f2 ->
		let cons = LRmap.add (LR.neg split) (f2, ex) cons in
		(LRset.add split spl, cons,acc)
	      | Some f1, Some f2 ->
		let cons = LRmap.add split (f1, ex) cons in
		let cons = LRmap.add (LR.neg split) (f2, ex) cons in
		(LRset.add split spl, cons,acc) in
    let spl, cons, eqs = 
      L.fold_left
        (fun (spl,cons,eqs) (a,_,e) ->
          let a = LR.make a in
          let spl = LRset.remove (LR.neg a) (LRset.remove a spl) in
          let(spl,cons,eqs) = 
            List.fold_left 
	      (fun acc (fact, ex) -> h_conseq acc fact (Ex.union ex e))
              (spl,cons,eqs) (LRmap.find a cons) in
          spl, cons, eqs
        )(env.split, env.conseq, eqs) la
    in
    {env with split=spl; conseq=cons}, eqs

  let assume env la ~are_eq ~are_neq ~class_of =
    Debug.assume fmt la; 
    let fct acc r =
      match X.term_extract r with
        | Some t -> 
          let {T.xs=xs} = T.view t in
          let res = List.fold_left (assume_one are_eq are_neq class_of)
	    acc (t::xs) in res

        | None   -> acc
    in 
    try (
      let env, splits, assume, conseq =
	List.fold_left (fun ((env,splits, assume, conseq) as acc) (a,_,ex) ->
	  match a with
	    | A.Builtin (b, s, [st;e1;e2]) when Hstring.equal s hReach ->
		let r = {rst = st; re1 = e1; re2 = e2} in
		add_R env r ex b
		  (splits, assume, conseq)
	    | A.Eq (t1,t2) -> fct (fct acc t1) t2
	    | A.Builtin (_,_,l) | A.Distinct (_, l) -> L.fold_left fct acc l)
	  (env, env.split, ESet.empty, env.conseq) la in
      let env = {env with split=splits; conseq=conseq} in
      let env, assume =
	implied_consequences are_eq are_neq env assume la in
      Debug.env fmt env;
      Debug.new_equalities fmt assume;
      (env,
       { assume = ESet.fold (fun (a, e) acc -> (LSem (LR.view a), e)::acc) assume [];
	 remove = [] }))
    with Unsat e -> 
      (env, { assume = [LTerm A.LT.faux, e];
			    remove = [] } )
end
