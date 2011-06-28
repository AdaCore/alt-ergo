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

open Options
open Format
open Why_ptree
open Common

module M = Map.Make(String)
module S = Set.Make(String)
module Sy = Symbols.Set

module MString = 
  Map.Make(struct type t = string let compare = Pervasives.compare end)

module Types = struct

  type t = (int * string list) MString.t

  let empty = MString.empty

  let bad_arity =
    let rec check s = function
      | [] -> false
      | v :: l -> S.mem v s || check (S.add v s) l
    in
    check S.empty
      
  let add env v id lc loc = 
    if MString.mem id env then error (ClashType id) loc;
    if bad_arity v then error TypeBadArityDecl loc;
    MString.add id (List.length v, lc) env
      
  let valid env v s loc = try
    let (n, lc) = MString.find s env in
    if List.length v <> n  then error (WrongArity(s,n)) loc; 
    lc
  with Not_found -> error (UnknownType s) loc
    
end

module Profile = struct

  type t = Ty.t list * Ty.t

  let of_logictype env p = 
    let htbl = Hashtbl.create 17 in
    let rec of_puretype = function
      | PPTint -> Ty.Tint
      | PPTbool -> Ty.Tbool
      | PPTreal -> Ty.Treal
      | PPTunit -> Ty.Tunit
      | PPTbitv n -> Ty.Tbitv n
      | PPTvarid (s, _) -> 
	  begin
	    try Ty.Tvar(Hashtbl.find htbl s)
	    with Not_found-> 
	      let nv = Ty.fresh_var () in
	      Hashtbl.add htbl s nv;
	      Ty.Tvar nv
	  end
      | PPTexternal (l, s, loc) when s = "farray" ->
        begin match l with
          | [t2] -> Ty.Tfarray (Ty.Tint,of_puretype t2)
          | [t1;t2] -> Ty.Tfarray (of_puretype t1,of_puretype t2)
          | _ -> error (WrongArity(s,2)) loc end
      | PPTexternal (l, s, loc) ->
	  let lc = Types.valid env l s loc in
	  if lc = [] then
	    Ty.text (List.map of_puretype l) s
	  else
	    Ty.tsum s lc
    in
    match p with
	PPredicate l -> List.map of_puretype l , Ty.Tbool
      | PFunction([],PPTvarid(_,loc)) -> 
	  error CannotGeneralize loc
      | PFunction(l,t) -> List.map of_puretype l , of_puretype t

  (* create fresh type variables each time it is called *)
  let fresh (l,ty) = 
    let hvars = Hashtbl.create 17 in
    let rec freshrec = function
      | Ty.Tvar {Ty.v=x} -> 
	  (try Ty.Tvar(Hashtbl.find hvars x) 
	   with Not_found -> 
	     let nv = Ty.fresh_var() in 
	     Hashtbl.add hvars x nv; Ty.Tvar nv)
      | Ty.Text(l,s) -> Ty.Text(List.map freshrec l,s)
      | Ty.Tfarray(t1,t2) -> Ty.Tfarray(freshrec t1,freshrec t2)
      | t -> t
    in
    List.map (fun t->freshrec (Ty.shorten t)) l , freshrec (Ty.shorten ty)

end

module Logics = struct

  type t = (Symbols.t * Profile.t) MString.t

  let empty = MString.empty 

  let add env pf loc name_kind n = 
    let sy = Symbols.name n ~kind:name_kind in
    if MString.mem n env then error (SymbAlreadyDefined n) loc;
    MString.add n (sy,pf) env

  let fresh env n loc = try
      let s, ty = MString.find n env in 
      s, Profile.fresh ty
  with Not_found -> error (SymbUndefined n) loc

end
    
module Env = struct

  type t = { 
    var_map : (Symbols.t * Ty.t) M.t ; (* variables' map*)
    tvar_map : Ty.t M.t ; (* typed variables' map *)
    types_map : Types.t ; 
    logics_map : Logics.t
  }

  let empty = { 
    var_map = M.empty;  
    tvar_map = M.empty;
    types_map = Types.empty;
    logics_map = Logics.empty
  }

  let rec of_puretype env create_var ty = 
    match ty with
      | PPTint -> Ty.Tint, env
      | PPTbool -> Ty.Tbool, env
      | PPTunit -> Ty.Tunit, env
      | PPTreal -> Ty.Treal, env
      | PPTbitv n -> Ty.Tbitv n, env
      | PPTvarid (s, _) -> 
	  begin
	    try M.find s env.tvar_map, env
	    with Not_found-> 
	      let nv =  create_var() in 
	      nv, { env with tvar_map = M.add s nv env.tvar_map } 
	  end
      | PPTexternal (l, s, loc) when s = "farray" ->
        let t1,t2 = match l with
          | [t2] -> PPTint,t2
          | [t1;t2] -> t1,t2
          | _ -> error (WrongArity(s,2)) loc in
	  let ty1, env = of_puretype env create_var t1 in
          let ty2, env = of_puretype env create_var t2 in
	  Ty.Tfarray (ty1,ty2), env
      | PPTexternal (l, s, loc) ->
	  let lc = Types.valid env.types_map l s loc in
	  if lc <> [] then
	    Ty.tsum s lc, env
	  else
	    let env , l = 
	      List.fold_left 
		(fun (env, l) t -> 
		   let ty , env = of_puretype env create_var t in
		   env , ty::l) 
	      (env, []) l 
	    in
	    Ty.text (List.rev l) s, env

  let add_raw env x sx ty = 
    { env with var_map = M.add x (sx, ty) env.var_map }

  let add create_symb create_var =
    List.fold_left
      (fun env (l, pty) ->
	 let ty , env = of_puretype env create_var pty in
	 List.fold_left 
	   (fun env x -> let sx = create_symb x in add_raw env x sx ty)
	   env l)

  let add_var = add Symbols.var (fun () -> Ty.Tvar (Ty.fresh_var ()))

  let add_name = add Symbols.name Ty.fresh_empty_text

  let add_logics env loc ac lp ty = 
    let prof = Profile.of_logictype env.types_map ty in
    let lmap = 
      List.fold_left 
	(fun lmap -> Logics.add lmap prof loc ac) env.logics_map lp
    in
    {env with logics_map = lmap }

  let find {var_map=m} n = M.find n m

  let mem n {var_map=m} = M.mem n m

  let list_of {var_map=m} = M.fold (fun _ c acc -> c::acc) m []

  let add_type_decl env v id lc loc =  
    { env with types_map = Types.add env.types_map v id lc loc }

  let fresh_type env = Logics.fresh env.logics_map
      
end



let new_id = 
  let r = ref 0 in 
  let next () = 
    r := !r+1; !r 
  in next


let rec freevars_term acc t = match t.c.tt_desc with
  | TTvar x -> Sy.add x acc
  | TTapp (_,lt) -> List.fold_left freevars_term acc lt
  | TTinfix (t1,_,t2) | TTget(t1, t2) -> 
      List.fold_left freevars_term acc [t1; t2]
  | TTset(t1, t2, t3) ->
      List.fold_left freevars_term acc [t1; t2; t3]
  | _ -> acc
      
let freevars_atom a = match a.c with
  | TAeq lt | TAneq lt | TAle lt
  | TAlt lt | TAbuilt(_,lt) | TAdistinct lt ->
      List.fold_left freevars_term Sy.empty lt
  | TApred t -> freevars_term  Sy.empty t
  | _ -> Sy.empty
      
let rec freevars_form f = match f with
  | TFatom a -> freevars_atom a
  | TFop (_,lf) ->
      List.fold_left Sy.union Sy.empty 
	(List.map (fun f -> freevars_form f.c) lf)
  | TFforall qf | TFexists qf -> 
      let s = freevars_form qf.qf_form.c in
      List.fold_left (fun acc (s,_) -> Sy.remove s acc) s qf.qf_bvars
  | TFlet(up,v,t,f) -> freevars_term (Sy.remove v (freevars_form f.c)) t
  | TFnamed(_, f) -> freevars_form f.c

let symbol_of = function
    PPadd -> Symbols.Op Symbols.Plus
  | PPsub -> Symbols.Op Symbols.Minus
  | PPmul -> Symbols.Op Symbols.Mult
  | PPdiv -> Symbols.Op Symbols.Div
  | PPmod ->  Symbols.Op Symbols.Modulo
  | _ -> assert false  

let rec type_term env f = 
  let e,t = type_term_desc env f.pp_loc f.pp_desc in
  {c = { tt_desc = e ; tt_ty = t }; annot = new_id ()}

and type_term_desc env loc = function
  | PPconst ConstTrue -> 
      TTconst Ttrue, Ty.Tbool
  | PPconst ConstFalse -> 
      TTconst Tfalse, Ty.Tbool
  | PPconst ConstVoid -> 
      TTconst Tvoid, Ty.Tunit
  | PPconst (ConstInt n) -> 
      TTconst(Tint n), Ty.Tint
  | PPconst (ConstReal n) -> 
      TTconst(Treal n), Ty.Treal
  | PPconst (ConstBitv n) -> 
      TTconst(Tbitv n), Ty.Tbitv (String.length n)
  | PPvar p -> 
      begin
	try let s,t = Env.find env p in TTvar s , t
	with Not_found -> 
	  match Env.fresh_type env p loc with
	    | s, ([], ty) -> TTvar s , ty 
	    | _ -> error (ShouldBeApply p) loc
      end
  | PPapp(p,args) -> 
      begin
	let te_args = List.map (type_term env) args in
	let lt_args =  List.map (fun {c={tt_ty=t}} -> t) te_args in
	let s, (lt, t) = Env.fresh_type env p loc in
	try
	  List.iter2 Ty.unify lt lt_args; 
	  TTapp(s,te_args), t
	with 
	  | Ty.TypeClash(t1,t2) -> 
	      error (Unification(t1,t2)) loc
	  | Invalid_argument _ -> 
	      error (WrongNumberofArgs p) loc
      end
  | PPinfix(t1,(PPadd | PPsub | PPmul | PPdiv as op),t2) ->
      begin
	let s = symbol_of op in
	let te1 = type_term env t1 in
	let te2 = type_term env t2 in
	let ty1 = Ty.shorten te1.c.tt_ty in
	let ty2 = Ty.shorten te2.c.tt_ty in
	match ty1, ty2 with
	    Ty.Tint, Ty.Tint -> TTinfix(te1,s,te2) , ty1
	  | Ty.Treal, Ty.Treal -> TTinfix(te1,s,te2), ty2
	  | Ty.Tint, _ -> error (ShouldHaveType(ty2,Ty.Tint)) t2.pp_loc
	  | Ty.Treal, _ -> error (ShouldHaveType(ty2,Ty.Treal)) t2.pp_loc
	  | _ -> error (ShouldHaveTypeIntorReal ty1) t1.pp_loc
      end
 | PPinfix(t1, PPmod, t2) ->
      begin
	let s = symbol_of PPmod in
	let te1 = type_term env t1 in
	let te2 = type_term env t2 in
	let ty1 = Ty.shorten te1.c.tt_ty in
	let ty2 = Ty.shorten te2.c.tt_ty in
	match ty1, ty2 with
	    Ty.Tint, Ty.Tint -> TTinfix(te1,s,te2) , ty1
	  | _ -> error (ShouldHaveTypeInt ty1) t1.pp_loc
      end
  | PPprefix(PPneg, {pp_desc=PPconst (ConstInt n)}) -> 
      TTconst(Tint ("-"^n)), Ty.Tint
  | PPprefix(PPneg, {pp_desc=PPconst (ConstReal n)}) -> 
      TTconst(Treal (Num.minus_num n)), Ty.Treal
  | PPprefix(PPneg, e) -> 
	let te = type_term env e in
	let ty = Ty.shorten te.c.tt_ty in
	if ty<>Ty.Tint && ty<>Ty.Treal then
	  error (ShouldHaveTypeIntorReal ty) e.pp_loc;
	TTprefix(Symbols.Op Symbols.Minus, te), ty
  | PPconcat(t1, t2) ->
      begin
	let te1 = type_term env t1 in
	let te2 = type_term env t2 in
	let ty1 = Ty.shorten te1.c.tt_ty in
	let ty2 = Ty.shorten te2.c.tt_ty in
	match ty1, ty2 with
	    Ty.Tbitv n , Ty.Tbitv m -> TTconcat(te1, te2), Ty.Tbitv (n+m)
	  | Ty.Tbitv _ , _ -> error (ShouldHaveTypeBitv ty2) t2.pp_loc
	  | _ , Ty.Tbitv _ -> error (ShouldHaveTypeBitv ty1) t1.pp_loc
	  | _ -> error (ShouldHaveTypeBitv ty1) t1.pp_loc
      end
  | PPextract(e, ({pp_desc=PPconst(ConstInt i)} as ei),
	      ({pp_desc=PPconst(ConstInt j)} as ej)) ->
      begin
	let te = type_term env e in
	let tye = Ty.shorten te.c.tt_ty in
	let i = int_of_string i in
	let j = int_of_string j in
	match tye with
	    Ty.Tbitv n -> 
	      if i>j then error (BitvExtract(i,j)) loc;
	      if j>=n then error (BitvExtractRange(n,j) ) loc;
	      let tei = type_term env ei in
	      let tej = type_term env ej in
	      TTextract(te, tei, tej), Ty.Tbitv (j-i+1)
	  | _ -> error (ShouldHaveType(tye,Ty.Tbitv (j+1))) loc
      end
  | PPget (t1, t2) ->
      begin
	let te1 = type_term env t1 in
	let te2 = type_term env t2 in
	let tyarray = Ty.shorten te1.c.tt_ty in
	let tykey2 = Ty.shorten te2.c.tt_ty in
	match tyarray with
	    Ty.Tfarray (tykey,tyval) ->
	      begin try
	              Ty.unify tykey tykey2;
                      TTget(te1, te2), tyval
	        with
	          | Ty.TypeClash(t1,t2) ->
	            error (Unification(t1,t2)) loc
              end
	  | _ ->
	    error ShouldHaveTypeArray t1.pp_loc
      end
  | PPset (t1, t2, t3) ->
      begin
	let te1 = type_term env t1 in
	let te2 = type_term env t2 in
	let te3 = type_term env t3 in
	let ty1 = Ty.shorten te1.c.tt_ty in
	let tykey2 = Ty.shorten te2.c.tt_ty in
	let tyval2 = Ty.shorten te3.c.tt_ty in
	try
	  match ty1 with
	    | Ty.Tfarray (tykey,tyval) ->
		Ty.unify tykey tykey2;Ty.unify tyval tyval2;
		TTset(te1, te2, te3), ty1
	    | _ -> error ShouldHaveTypeArray t1.pp_loc
	with
	  | Ty.TypeClash(t, t') -> 
	      error (Unification(t, t')) loc
      end
  | PPif(t1,t2,t3) ->
      begin
	let te1 = type_term env t1 in
	let ty1 = Ty.shorten te1.c.tt_ty in
	if not (Ty.equal ty1 Ty.Tbool) then 
	  error (ShouldHaveType(ty1,Ty.Tbool)) t1.pp_loc;
	let te2 = type_term env t2 in
	let te3 = type_term env t3 in
	let ty2 = Ty.shorten te2.c.tt_ty in
	let ty3 = Ty.shorten te3.c.tt_ty in
	if not (Ty.equal ty2 ty3) then
	  error (ShouldHaveType(ty3,ty2)) t3.pp_loc;
	TTapp(Symbols.name "ite",[te1;te2;te3]) , ty2
      end
  | PPnamed(lbl, t) -> 
      let t = type_term env t in
      t.c.tt_desc, t.c.tt_ty

  | PPlet(x,t1,t2) ->
      let te1 = type_term env t1 in
      let ty1 = Ty.shorten te1.c.tt_ty in
      let sx = Symbols.name x in
      let env = Env.add_raw env x sx ty1 in 
      let te2 = type_term env t2 in
      let ty2 = Ty.shorten te2.c.tt_ty in
      let s, _ = Env.find env x in
      TTlet(s, te1, te2), ty2
      
  | _ -> error SyntaxError loc


let rec join_forall f = match f.pp_desc with
    PPforall(vs,ty,trs1,f) -> 
      let tyvars,trs2,f = join_forall f in  
      (vs,ty)::tyvars , trs1@trs2 , f
  | PPnamed(lbl, f) -> 
      join_forall f
  | _ -> [] , [] , f

let rec join_exists f = match f.pp_desc with
  | PPexists (vars, ty, f) -> 
      let tyvars,f = join_exists f in  
      (vars, ty)::tyvars ,  f
  | PPnamed (_, f) -> join_exists f
  | _ -> [] , f

let make_le_or_lt p l = 
  let s = match p with PPle -> "<=" | PPlt -> "<" | _ -> assert false in
  try 
    let _ = Builtin.is_builtin s in 
    (match p with 
      | PPle -> TAle l
      | PPlt -> TAlt l
      | _ -> assert false)
  with Not_found -> 
    let s = Symbols.name s in (* XXX *)
    let t2 = {c={tt_desc=TTconst Ttrue;tt_ty=Ty.Tbool}; annot=new_id ()} in
    let t1 = {c={tt_desc=TTapp(s,l);tt_ty=Ty.Tbool}; annot=new_id ()} in 
    TAeq [t1;t2]

let rec type_form env f = 
  let form, vars = (match f.pp_desc with
    | PPconst ConstTrue -> 
      TFatom {c=TAtrue; annot=new_id ()}, Sy.empty
    | PPconst ConstFalse -> 
      TFatom {c=TAfalse; annot=new_id ()}, Sy.empty
    | PPvar p ->
      let r = begin
	match Env.fresh_type env p f.pp_loc with
	  | s, ([] ,Ty.Tbool) -> 
	    (try 
	       TFatom {c = TAbuilt(Builtin.is_builtin p,[]);
		       annot = new_id() }
	     with Not_found -> 
	       let t2 = {c = {tt_desc=TTconst Ttrue;tt_ty=Ty.Tbool};
			 annot = new_id ()} in
	       let t1 = {c = {tt_desc=TTvar s; tt_ty=Ty.Tbool};
			 annot = new_id ()} in
	       TFatom {c = TAeq [t1;t2]; annot=new_id ()})
	  | _ -> error (NotAPropVar p) f.pp_loc
      end in r, freevars_form r
	
    | PPapp(p,args ) ->
      let r = 
	begin
	  let te_args = List.map (type_term env) args in
	  let lt_args =  List.map (fun {c={tt_ty=t}} -> t) te_args in
	  match Env.fresh_type env p f.pp_loc with
	    | s , (lt,Ty.Tbool) -> 
	      begin
		try
		  List.iter2 Ty.unify lt lt_args;
		  (try 
		     TFatom { c = TAbuilt(Builtin.is_builtin p,te_args);
			      annot=new_id ()}
		   with Not_found -> 
		     let t1 = {c = {tt_desc=TTapp(s,te_args); tt_ty=Ty.Tbool};
			       annot=new_id ()} in
		     (* TFatom (TAeq[t1;{tt_desc=TTtrue;tt_ty=Ty.Tbool}]) *)
		     TFatom { c = TApred t1; annot=new_id () })
		with 
		    Ty.TypeClash(t1,t2) -> error (Unification(t1,t2)) f.pp_loc
		  | Invalid_argument _ -> error (WrongNumberofArgs p) f.pp_loc
	      end
	    | _ -> error (NotAPredicate p) f.pp_loc
	end 
      in r, freevars_form r
	
    | PPreach(t1, t2, t3) ->
      let r = 
	begin
	  let te1 = type_term env t1 in
	  let te2 = type_term env t2 in
	  let te3 = type_term env t3 in
	  let ty1 = te1.c.tt_ty in
	  let tykey2 = te2.c.tt_ty in
	  let tykey3 = te3.c.tt_ty in
	  try
	    match ty1 with
	      | Ty.Tfarray (tykey, _) ->
		Ty.unify tykey tykey2; Ty.unify tykey tykey3;
		  TFatom 
		    { c = TAbuilt(Builtin.is_builtin "reach", [te1;te2;te3]);
		      annot=new_id () } 
	      | _ -> error ShouldHaveTypeArray t1.pp_loc
	  with
	    | Ty.TypeClash(t, t') -> 
	      error (Unification(t, t')) t1.pp_loc
	end
      in r, freevars_form r
	    
    | PPdistinct (args) ->
      let r = 
	begin
	  let te_args = List.map (type_term env) args in
	  let lt_args =  List.map (fun {c={tt_ty=t}} -> t) te_args in
	  try
	    let t = match lt_args with
	      | t::_ -> t
	      | [] ->
		  error (WrongNumberofArgs "distinct") f.pp_loc
	    in
	    List.iter (Ty.unify t) lt_args; 
	    TFatom { c = TAdistinct te_args; annot=new_id () }
	  with 
	    | Ty.TypeClash(t1,t2) -> error (Unification(t1,t2)) f.pp_loc
	end
      in r, freevars_form r

    | PPinfix 
	({pp_desc = PPinfix (_, (PPlt|PPle|PPgt|PPge|PPeq|PPneq), a)} as p, 
	 (PPlt | PPle | PPgt | PPge | PPeq | PPneq as r), b) ->
      let r = 
        let q = { pp_desc = PPinfix (a, r, b); pp_loc = f.pp_loc } in
        let f1,_ = type_form env p in
        let f2,_ = type_form env q in
        TFop(OPand, [f1;f2])
      in r, freevars_form r
    | PPinfix(t1, (PPlt | PPgt | PPle | PPge | PPeq | PPneq as op) ,t2) -> 
      let r = begin
	let tt1 = type_term env t1 in
	let tt2 = type_term env t2 in
	try
	  Ty.unify tt1.c.tt_ty tt2.c.tt_ty;
	  match op with
	    | PPeq -> TFatom {c = TAeq [tt1;tt2]; annot=new_id ()}
	    | PPneq -> TFatom {c = TAneq [tt1;tt2]; annot=new_id ()}
	    | _ ->
	      let ty = Ty.shorten tt1.c.tt_ty in
	      match ty with
		| Ty.Tint | Ty.Treal -> begin 
		  match op with
		    | PPle ->
		      TFatom {c = make_le_or_lt PPle [tt1;tt2];
			      annot = new_id ()}
		    | PPge ->
		      TFatom {c = make_le_or_lt PPle [tt2;tt1];
			      annot = new_id ()}
		    | PPlt -> begin match ty with
			| Ty.Tint -> 
			  let one = 
			    { c = {tt_ty = Ty.Tint ;
				   tt_desc = TTconst(Tint "1")};
				annot = new_id () } in
			  let desc = 
			    TTinfix(tt2, Symbols.Op Symbols.Minus,one)
			  in
			  TFatom { c = (make_le_or_lt PPle 
				  [tt1;{tt2 with c={tt2.c with tt_desc=desc}}]);
				   annot = new_id ()}
			| _ -> 
			  TFatom { c = make_le_or_lt PPlt [tt1;tt2];
				   annot = new_id ()}
		    end
		    | PPgt -> begin match ty with
			| Ty.Tint ->
			  let one = 
			    { c = {tt_ty = Ty.Tint ;
				   tt_desc = TTconst(Tint "1")};
				annot = new_id () } in
			  let desc = 
			    TTinfix(tt1, Symbols.Op Symbols.Minus, one) 
			  in
			  TFatom { c = (make_le_or_lt PPle
				 [tt2;{tt1 with c={tt1.c with tt_desc=desc}}]);
			      	   annot = new_id ()}
			| _ -> 
			  TFatom { c = make_le_or_lt PPlt [tt2;tt1];
				   annot = new_id () }
		    end
		    | _ -> assert false
		end
		| _ -> error (ShouldHaveTypeIntorReal ty) t1.pp_loc
	with Ty.TypeClash(t1,t2) -> error (Unification(t1,t2)) f.pp_loc
      end in r, freevars_form r
    | PPinfix(f1,op ,f2) -> 
      begin
	let f1,fv1 = type_form env f1 in
	let f2,fv2 = type_form env f2 in
	((match op with
	  | PPand -> 
	    TFop(OPand,[f1;f2])
	  | PPor -> TFop(OPor,[f1;f2])
	  | PPimplies -> TFop(OPimp,[f1;f2])
	  | PPiff -> TFop(OPiff,[f1;f2])
	  | _ -> assert false), Sy.union fv1 fv2)
      end
    | PPprefix(PPnot,f) -> 
      let f, fv = type_form env f in TFop(OPnot,[f]),fv
    | PPif(f1,f2,f3) -> 
      let f1 = type_term env f1 in
      let f2,fv2 = type_form env f2 in
      let f3,fv3 = type_form env f3 in
      TFop(OPif f1,[f2;f3]), Sy.union fv2 fv3
    | PPnamed(lbl,f) -> 
      let f, fv = type_form env f in
      let lbl = Hstring.make lbl in
      TFnamed(lbl, f), fv
    | PPforall _ | PPexists _ ->
      let ty_vars, ty, triggers, f' = 
	match f.pp_desc with 
	  | PPforall(vars,ty,triggers,f') -> 
	    let ty_vars, triggers', f' = join_forall f' in
	    (vars, ty)::ty_vars,ty ,triggers@triggers', f'
	  | PPexists(vars,ty,f') -> 
	    let ty_vars, f' = join_exists f' in
	    (vars, ty)::ty_vars, ty, [], f'
	  | _ -> assert false
      in
      let env' = Env.add_var env ty_vars in
      let f', fv = type_form env' f' in
      let ty_triggers = List.map (List.map (type_term env')) triggers in
      let upbvars = Env.list_of env in
      let bvars = 
	List.fold_left 
	  (fun acc (l,_) -> 
	    let tys = List.map (Env.find env') l in
	    let tys = List.filter (fun (s,_) -> Sy.mem s fv) tys in
	    tys @ acc) [] ty_vars in 
      let qf_form = {
	qf_upvars = upbvars ; 
	qf_bvars = bvars ;
	qf_triggers = ty_triggers ;
	qf_form = f'}
      in
      (match f.pp_desc with 
	  PPforall _ -> TFforall qf_form
	| _ -> Existantial.make qf_form), 
      (List.fold_left (fun acc (l,_) -> Sy.remove l acc) fv bvars)
    | PPlet (var,t,f) -> 
      let {c= { tt_ty = ttype }} as tt = type_term env t in
      let svar = Symbols.var var in
      let up = Env.list_of env in
      let env = {env with 
	Env.var_map = M.add var (svar, ttype) env.Env.var_map} in
      let f,fv = type_form env f in
      TFlet (up ,svar , tt, f), freevars_term (Sy.remove svar fv) tt
    | _ -> error ShouldHaveTypeProp f.pp_loc)
  in
  {c = form; annot = new_id ()}, vars


let make_rules loc f = match f.c with
  | TFforall {qf_bvars = vars; qf_form = {c = TFatom {c = TAeq [t1; t2]}}} ->
      {rwt_vars = vars; rwt_left = t1; rwt_right = t2}
  | TFatom {c = TAeq [t1; t2]} -> 
      {rwt_vars = []; rwt_left = t1; rwt_right = t2}
  | _ -> error SyntaxError loc


let fresh_var = 
  let cpt = ref 0 in
  fun x -> incr cpt; ("_"^x^(string_of_int !cpt))

let rec alpha_renaming s f =
  { f with pp_desc = alpha_rec s f.pp_desc }
and alpha_rec ((up, m) as s) f = 
  match f with
    | PPvar x ->
	begin 
	  try
	    let y = M.find x m in
	    PPvar y
	  with Not_found -> f 
	end
    | PPapp(k, l) -> 
	PPapp(k, List.map (alpha_renaming s) l)
    | PPdistinct l -> 
	PPdistinct (List.map (alpha_renaming s) l)
    | PPconst _ -> f
    | PPinfix(f1, op, f2) -> 
	let ff1 = alpha_renaming s f1 in
	let ff2 = alpha_renaming s f2 in
	PPinfix(ff1, op, ff2)
    | PPprefix(op, f1) ->
	PPprefix(op, alpha_renaming s f1)
    | PPget(f1,f2) ->
	let ff1 = alpha_renaming s f1 in
	let ff2 = alpha_renaming s f2 in
	PPget(ff1, ff2)
    | PPset(f1, f2, f3) ->
	let ff1 = alpha_renaming s f1 in
	let ff2 = alpha_renaming s f2 in
	let ff3 = alpha_renaming s f3 in
	PPset(ff1, ff2, ff3)
    | PPreach(f1, f2, f3) ->
	let ff1 = alpha_renaming s f1 in
	let ff2 = alpha_renaming s f2 in
	let ff3 = alpha_renaming s f3 in
	PPreach(ff1, ff2, ff3)
    | PPextract(f1, f2, f3) ->
	let ff1 = alpha_renaming s f1 in
	let ff2 = alpha_renaming s f2 in
	let ff3 = alpha_renaming s f3 in
	PPextract(ff1, ff2, ff3)
    | PPconcat(f1, f2) ->
	let ff1 = alpha_renaming s f1 in
	let ff2 = alpha_renaming s f2 in
	PPconcat(ff1, ff2)
    | PPif(f1, f2, f3) ->
	let ff1 = alpha_renaming s f1 in
	let ff2 = alpha_renaming s f2 in
	let ff3 = alpha_renaming s f3 in
	PPif(ff1, ff2, ff3)
    | PPnamed(n, f1) ->
	PPnamed(n, alpha_renaming s f1)
    | PPforall(xs, ty, trs, f1) ->
	let xs1, xs2 = List.partition (fun x -> S.mem x up) xs in
	let nv = List.map fresh_var xs1 in
	let m = List.fold_left2 (fun m x nx -> M.add x nx m) m xs1 nv in
	let xs = nv@xs2 in
	let up = List.fold_left (fun up x -> S.add x up) up xs in
	let s = (up, m) in
	let ff1 = alpha_renaming s f1 in
	let trs = List.map (List.map (alpha_renaming s)) trs in
	PPforall(xs, ty, trs, ff1)
    | PPlet(x, f1, f2) ->
	let ff1 = alpha_renaming s f1 in
	let s, x = 
	  if S.mem x up then
	    let nx = fresh_var x in
	    let m = M.add x nx m in
	    let up = S.add nx up in
	    (up, m), nx
	  else
	    (S.add x up, m), x
	in
	let ff2 = alpha_renaming s f2 in
	PPlet(x, ff1, ff2)
	
    | PPexists(lx, ty, f1) ->
	let s, lx = 
	  List.fold_left
	    (fun (s, lx) x ->
	       if S.mem x up then
		 let nx = fresh_var x in
		 let m = M.add x nx m in
		 let up = S.add nx up in
		 (up, m), nx :: lx
	       else
		 (S.add x up, m), x :: lx)
	    (s, []) lx
	in
	let ff1 = alpha_renaming s f1 in
	PPexists(lx, ty, ff1)
 
let alpha_renaming = alpha_renaming (S.empty, M.empty)

let inv_infix = function 
  | PPand -> PPor | PPor -> PPand | _ -> assert false

let rec elim_toplevel_forall env bnot f = 
  (* bnot = true : nombre impaire de not *)
  match f.pp_desc with
    | PPforall(lv,t,_,f) when bnot-> 
	elim_toplevel_forall (Env.add_name env [lv,t]) bnot f

    | PPinfix(f1,PPand,f2) when not bnot -> 
	let env , f1 = elim_toplevel_forall env false f1 in
	let env , f2 = elim_toplevel_forall env false f2 in
	env , { f with pp_desc = PPinfix(f1, PPand , f2)}
	
    | PPinfix(f1, PPor,f2) when bnot -> 
	let env , f1 = elim_toplevel_forall env true f1 in
	let env , f2 = elim_toplevel_forall env true f2 in
        env , { f with pp_desc = PPinfix(f1, PPand , f2)}

    | PPinfix(f1,PPimplies,f2) when bnot -> 
        let env , f1 = elim_toplevel_forall env false f1 in
	let env , f2 = elim_toplevel_forall env true f2 in
	  env , { f with pp_desc = PPinfix(f1,PPand,f2)}
	
    | PPprefix(PPnot,f) -> elim_toplevel_forall env (not bnot) f

    | _ when bnot -> 
	env , { f with pp_desc=PPprefix(PPnot,f)}

    | _  -> env , f


let rec intro_hypothesis env valid_mode f = 
  match f.pp_desc with
    | PPinfix(f1,PPimplies,f2) when valid_mode -> 
	let env, f1 = elim_toplevel_forall env (not valid_mode) f1 in
	let env, axioms , goal = intro_hypothesis env valid_mode f2 in
	env, f1::axioms , goal
    | PPforall(lv, ty, _, f) when valid_mode ->  
	intro_hypothesis (Env.add_name env [lv, ty]) valid_mode f
    | PPexists(lv, ty, f) when not valid_mode-> 
	intro_hypothesis (Env.add_name env [lv, ty]) valid_mode f
    | _ -> 
	let env , f = elim_toplevel_forall env valid_mode f in
	env , [] , f

(*
let rec move_up f = 
  { f with pp_desc = move_up_desc f.pp_desc }

and move_up_desc = function
  | PPinfix(f1,op,f2) ->
      PPinfix(move_up f1,op,move_up f2)
	
  | PPprefix(op,f1) ->
      PPprefix(op,move_up f1)
	
  | PPif(f1,f2,f3) ->
      PPif(move_up f1, move_up f2, move_up f3)
	
  | PPforall(lv1,t1,[],
	     ({pp_desc=
		  PPinfix(fl,op,({pp_desc=PPforall(lv2,t2,[],f2)} as ff))} 
		as fd)) ->
      let ff = { ff with pp_desc = PPinfix(fl,op,f2)} in
      let fd = {fd with pp_desc=PPforall(lv2,t2,[],ff)} in
      PPforall(lv1,t1,[],fd)
	
    | f -> f
*)

let fresh_axiom_name = 
  let cpt = ref 0 in fun () -> incr cpt; "_H"^(string_of_int !cpt)

let check_duplicate_params l =
  let rec loop l acc =
    match l with
      | [] -> ()
      | (loc,x,_)::rem ->
	  if List.mem x acc then
	    error (ClashParam x) loc
	  else loop rem (x::acc)
  in
  loop l []

let rec make_pred loc trs f = function
    [] ->  f
  | [x,t] ->
      { pp_desc = PPforall([x],t,trs,f) ; pp_loc = loc }
  | (x,t)::l -> 
      { pp_desc = PPforall([x],t,[],(make_pred loc trs f l)) ; 
	pp_loc = loc }

let rec max_terms acc f = 
  match f.pp_desc with
    | PPinfix(f1, ( PPand | PPor | PPimplies | PPiff ), f2) 
    | PPconcat(f1, f2) ->  
	let acc = max_terms acc f1 in
	max_terms acc f2

    | PPforall(_, _, _, _) 
    | PPexists(_, _, _) 
    | PPvar _ 
    | PPlet(_, _, _) 
    | PPinfix(_, _, _) -> raise Exit

    | PPif(f1, f2, f3) ->
	let acc = max_terms acc f1 in
	let acc = max_terms acc f2 in
	max_terms acc f3
    | PPextract(f1, _, _) | PPprefix(_, f1) 
    | PPnamed(_, f1) ->
	max_terms acc f1
    | _ -> f::acc

let max_terms f = try max_terms [] f with Exit -> []

let rec mono_term {c = {tt_ty=tt_ty; tt_desc=tt_desc}; annot = id} = 
  let tt_desc = match tt_desc with
    | TTconst _ | TTvar _ -> 
        tt_desc
    | TTinfix (t1, sy, t2) -> 
        TTinfix(mono_term t1, sy, mono_term t2)
    | TTprefix (sy,t) -> 
        TTprefix(sy, mono_term t)
    | TTapp (sy,tl) -> 
        TTapp (sy, List.map mono_term tl)
    | TTget (t1,t2) ->
        TTget (mono_term t1, mono_term t2)
    | TTset (t1,t2,t3) -> 
        TTset(mono_term t1, mono_term t2, mono_term t3)
    | TTextract (t1,t2,t3) -> 
        TTextract(mono_term t1, mono_term t2, mono_term t3)
    | TTconcat (t1,t2)->
        TTconcat (mono_term t1, mono_term t2)
    | TTlet (sy,t1,t2)-> 
        TTlet (sy, mono_term t1, mono_term t2)
  in 
  { c = {tt_ty = Ty.monomorphize tt_ty; tt_desc=tt_desc}; annot = id}
 

let monomorphize_atom tat =
  let c = match tat.c with 
    | TAtrue | TAfalse -> tat.c
    | TAeq tl -> TAeq (List.map mono_term tl)
    | TAneq tl -> TAneq (List.map mono_term tl)
    | TAle tl -> TAle (List.map mono_term tl)
    | TAlt tl -> TAlt (List.map mono_term tl)
    | TAdistinct tl -> TAdistinct (List.map mono_term tl)
    | TApred t -> TApred (mono_term t)
    | TAbuilt (hs, tl) -> TAbuilt(hs, List.map mono_term tl)
  in 
  { tat with c = c }

let rec monomorphize_form tf = 
  let c = match tf.c with
    | TFatom tat -> TFatom (monomorphize_atom tat)
    | TFop (oplogic , tfl) ->
        TFop(oplogic, List.map monomorphize_form tfl)
    | TFforall qf ->
        TFforall
          {qf with
             qf_form = monomorphize_form qf.qf_form;
             qf_triggers = List.map (List.map mono_term) qf.qf_triggers}

    | TFexists qf ->
        TFexists 
          {qf with
             qf_form = monomorphize_form qf.qf_form;
             qf_triggers = List.map (List.map mono_term) qf.qf_triggers}

    | TFlet (l, sy, tt, tf) ->
        TFlet(l,sy, mono_term tt, monomorphize_form tf)
    | TFnamed (hs,tf) ->
        TFnamed(hs, monomorphize_form tf)
  in 
  { tf with c = c }

let axioms_of_rules loc name lf acc env =
  let acc = 
    List.fold_left
      (fun acc (f, _) ->
        let f = Triggers.make false f in
        let name = (Common.fresh_string ()) ^ "_" ^ name in
        let td = {c = TAxiom(loc,name,f); annot = new_id () } in
	(td, env)::acc
      ) acc lf
  in 
  acc, env
      
let type_decl (acc, env) d = 
  try
    match d with
      | Logic (loc, ac, lp, ty) -> 
	  let env' = Env.add_logics env loc ac lp ty in
	  let td = {c = TLogic(loc,lp,ty); annot = new_id () } in
	  (td, env)::acc, env'

      | Axiom(loc,name,f) -> 
	  let f, _ = type_form env f in 
	  let f = Triggers.make false f in
	  let td = {c = TAxiom(loc,name,f); annot = new_id () } in
	  (td, env)::acc, env

      | Rewriting(loc, name, lr) -> 
	  let lf = List.map (type_form env) lr in
          if Options.rewriting then
            let rules = List.map (fun (f,_) -> make_rules loc f) lf in
	    let td = {c = TRewriting(loc, name, rules); annot = new_id () } in
	    (td, env)::acc, env
          else
            axioms_of_rules loc name lf acc env


      | Goal(loc,n,f) ->
	  (*let f = move_up f in*)
	  let f = alpha_renaming f in
	  let env', axioms, goal = 
	    intro_hypothesis env (not (!smtfile or !smt2file or !satmode)) f in
	  let acc =
	    List.fold_left
	      (fun acc f ->
		 let f,_ = type_form env' f in
		 let f = monomorphize_form f in
                 let f = Triggers.make false f in
		 let td = {c = TAxiom(loc, fresh_axiom_name(), f);
			   annot = new_id () } in
		 (td, env')::acc) acc axioms
	  in
	  let goal, _ = type_form env' goal in
          let goal = monomorphize_form goal in
	  let goal = Triggers.make true goal in
	  let td = {c = TGoal(loc, n, goal); annot = new_id () } in
	  (td, env')::acc, env

      | Predicate_def(loc,n,l,e) 
      | Function_def(loc,n,l,_,e) ->
	  check_duplicate_params l;
	  let ty = 
	    let l = List.map (fun (_,_,x) -> x) l in
	    match d with
		Function_def(_,_,_,t,_) -> PFunction(l,t) 
	      | _ -> PPredicate l 
	  in
	  let l = List.map (fun (_,x,t) -> (x,t)) l in

	  let env = Env.add_logics env loc Symbols.Other [n] ty in (* TODO *)

	  let lvar = List.map (fun (x,_) -> {pp_desc=PPvar x;pp_loc=loc}) l in
	  let p = {pp_desc=PPapp(n,lvar) ; pp_loc=loc } in
	  let infix = match d with Function_def _ -> PPeq | _ -> PPiff in
	  let f = { pp_desc = PPinfix(p,infix,e) ; pp_loc = loc } in
	  (* le trigger [[p]] ne permet pas de replier la definition,
	     donc on calcule les termes maximaux de la definition pour
	     laisser une possibilite de replier *)
	  let trs = max_terms e in
	  let f = make_pred loc ([p]::[trs]) f l in
	  let f,_ = type_form env f in
	  let f = Triggers.make false f in
	  let td = 
	    match d with 
	      | Function_def(_,_,_,t,_) -> TFunction_def(loc,n,l,t,f)
	      | _ ->  TPredicate_def(loc,n,l,f)
	  in
	  let td_a = { c = td; annot=new_id () } in
	  (td_a, env)::acc, env

      | TypeDecl(loc, ls, s, lc) -> 
	  let env1 = Env.add_type_decl env ls s lc loc in
	  let td1 =  TTypeDecl(loc, ls, s, lc) in
	  let td1_a = { c = td1; annot=new_id () } in
          let tls = List.map (fun s -> PPTvarid (s,loc)) ls in
	  let ty = PFunction([], PPTexternal(tls, s, loc)) in
	  let env2 = Env.add_logics env1 loc Symbols.Constructor lc ty in
	  let td2 = TLogic(loc, lc, ty) in
	  let td2_a = { c = td2; annot=new_id () } in
	  (td1_a, env1)::(td2_a,env2)::acc, env2

  with Warning(e,loc) -> 
    Loc.report loc; 
    acc, env

let file ld = 
  let ltd, _ = 
    List.fold_left 
      (fun acc d -> type_decl acc d)
      ([], Env.empty) ld
  in
  List.rev ltd

let split_goals l =
  let _, _, ret = 
    List.fold_left
      (fun (ctx, hyp, ret) ( (td, env) as x) -> 
	 match td.c with 
	   | TGoal _ -> ctx, [], (x::(hyp@ctx))::ret
	   | TAxiom (_, s, _) when String.length s > 0 && s.[0] = '_' ->
	       ctx, x::hyp, ret
	   | _ -> x::ctx, hyp, ret) ([],[],[]) l
  in 
  List.rev_map List.rev ret

let term env vars t =
  let vmap = 
    List.fold_left
      (fun m (s,ty)->
	 let str = Symbols.to_string s in
	 M.add str (s,ty) m
      ) env.Env.var_map vars in
  let env = { env with Env.var_map = vmap } in
  type_term env t



type env = Env.t
