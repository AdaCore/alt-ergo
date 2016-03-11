(******************************************************************************)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2015 --- OCamlPro                                   *)
(*     This file is distributed under the terms of the CeCILL-C licence       *)
(******************************************************************************)

(******************************************************************************)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*   This file is distributed under the terms of the CeCILL-C licence         *)
(******************************************************************************)

open Format
open Options
open Sig

module Z = Numbers.Z
module Q = Numbers.Q

let ale = Hstring.make "<="
let alt = Hstring.make "<"
let is_le n = Hstring.compare n ale = 0
let is_lt n = Hstring.compare n alt = 0

let (-@) l1 l2 = List.rev_append l1 l2

module L = Literal
module Sy = Symbols
module I = Intervals

exception NotConsistent of Literal.LT.Set.t

module type EXTENDED_Polynome = sig
  include Polynome.T
  val extract : r -> t option
  val embed : t -> r
end


module OracleContainer =
  (val (Inequalities.get_current ()) : Inequalities.Container_SIG)


module Make
  (X : Sig.X)
  (Uf : Uf.S with type r = X.r)
  (P : EXTENDED_Polynome with type r = X.r) = struct

    module MP = Map.Make(P)
    module SP = Set.Make(P)
    module SX = Set.Make(struct type t = X.r let compare = X.hash_cmp end)
    module MX = Map.Make(struct type t = X.r let compare = X.hash_cmp end)
    module MPL = Literal.LT.Map


    module Oracle = OracleContainer.Make(X)(Uf)(P)

    type r = P.r
    type uf = Uf.t
    module LR =
      Literal.Make(struct type t = X.r let compare = X.hash_cmp include X end)

    module MR = Map.Make(
      struct
        type t = r L.view
        let compare a b = LR.compare (LR.make a) (LR.make b)
      end)

    let alien_of p =  P.embed p
    let poly_of r =
      match P.extract r with
      | Some p -> p
      | None ->
        P.create
          [Numbers.Q.one, r] Numbers.Q.zero (X.type_info r)


    type t = {
      inequations : Oracle.t MPL.t;
      monomes: (I.t * SX.t) MX.t;
      polynomes : I.t MP.t;
      known_eqs : SX.t;
      improved : SP.t;
      classes : Term.Set.t list;
      size_splits : Q.t;
    }

    (*BISECT-IGNORE-BEGIN*)
    module Debug = struct

      let assume a expl =
        if debug_fm () then begin
	  fprintf fmt "[fm] We assume: %a@." LR.print (LR.make a);
	  fprintf fmt "explanations: %a@." Explanation.print expl
        end

      let print_use fmt use =
        SX.iter (fprintf fmt "%a, " X.print) use

      let env env =
        if debug_fm () then begin
	  fprintf fmt "------------ FM: inequations-------------------------@.";
          MPL.iter
            (fun a {Oracle.ple0=p; is_le=is_le} ->
              fprintf fmt "%a%s0  |  %a@."
                P.print p (if is_le then "<=" else "<") L.LT.print a
            )env.inequations;
          fprintf fmt "------------ FM: monomes ----------------------------@.";
	  MX.iter
	    (fun x (i, use) ->
	      fprintf fmt "%a : %a |-use-> {%a}@."
		X.print x I.print i print_use use)
	    env.monomes;
	  fprintf fmt "------------ FM: polynomes---------------------------@.";
	  MP.iter
	    (fun p i ->
	      fprintf fmt "%a : %a@."
		P.print p I.print i)
	    env.polynomes;
	  fprintf fmt "-----------------------------------------------------@."
        end

      let implied_equalities l =
        if debug_fm () then
          begin
            fprintf fmt "[fm] %d implied equalities@." (List.length l);
            List.iter
	      (fun (ra, _, ex, _) ->
                fprintf fmt "  %a %a@."
		  LR.print (LR.make ra) Explanation.print ex) l
          end

      let case_split r1 r2 =
	if debug_fm () then
	  fprintf fmt "[case-split] %a = %a@." X.print r1 X.print r2

      let no_case_split s =
	if debug_fm () then fprintf fmt "[case-split] %s : nothing@." s


      let inconsistent_interval expl =
	if debug_fm () then
	  fprintf fmt "interval inconsistent %a@." Explanation.print expl

      let added_inequation kind ineq =
        if debug_fm () then begin
          fprintf fmt "[fm] I derived the (%s) inequality: %a %s 0@."
            kind P.print ineq.Oracle.ple0 (if ineq.Oracle.is_le then "<=" else "<");
          fprintf fmt "from the following combination:@.";
          Literal.LT.Map.iter
            (fun a (coef, ple0, is_le) ->
              fprintf fmt "\t%a * (%a %s 0) + @."
                Q.print coef P.print ple0 (if is_le then "<=" else "<")
            )ineq.Oracle.dep;
          fprintf fmt "\t0@.@."
        end

    end
    (*BISECT-IGNORE-END*)

    let empty classes = {
      inequations = MPL.empty;
      monomes = MX.empty ;
      polynomes = MP.empty ;
      known_eqs = SX.empty ;
      improved = SP.empty ;
      classes = classes;
      size_splits = Q.one;
    }

    (*let up_improved env p oldi newi =
      if I.is_strict_smaller newi oldi then
      { env with improved = SP.add p env.improved }
      else env*)

    (** computes an interval for vars = x_1^n_1 * ..... * x_i^n_i
        (1) if some var is not in monomes, then return undefined
        (2) check that all vars are in monomes before doing interval ops **)
    let mult_bornes_vars vars monomes ty =
      try
        let l = List.rev_map (fun (y,n) -> fst (MX.find y monomes), n) vars in
        List.fold_left
          (fun ui (yi,n) -> I.mult ui (I.power n yi))
          (I.point Q.one ty Explanation.empty) l
      with Not_found -> I.undefined ty

    (** computes the interval of a polynome from those of its monomes.
        The monomes are supposed to be already added in env **)
    let intervals_from_monomes ?(monomes_inited=true) env p =
      let pl, v = P.to_list p in
      List.fold_left
        (fun i (a, x) ->
	  let i_x, _  =
            try MX.find x env.monomes
            with Not_found ->
              if monomes_inited then assert false;
              I.undefined (X.type_info x), SX.empty
          in
	  I.add (I.scale a i_x) i
        ) (I.point v (P.type_info p) Explanation.empty) pl


    let rec init_monomes_of_poly are_eq env p use_p expl =
      List.fold_left
        (fun env (_, x) ->
          try
            let u, old_use_x = MX.find x env.monomes in
            { env
              with monomes =
                MX.add x (u, SX.union old_use_x use_p) env.monomes }
          with Not_found ->
            update_monome are_eq expl use_p env x
        ) env (fst (P.to_list p))

    and init_alien are_eq expl p (normal_p, c, d) ty use_x env =
      let env = init_monomes_of_poly are_eq env p use_x expl in
      let i = intervals_from_monomes env p in
      let i =
        try
	  let old_i = MP.find normal_p env.polynomes in
	  let old_i = I.scale d
	    (I.add old_i (I.point c ty Explanation.empty)) in
	  I.intersect i old_i
        with Not_found -> i
      in
      env, i



    and update_monome are_eq expl use_x env x =
      let ty = X.type_info x in
      let ui, env = match  X.ac_extract x with
        | Some {h=h; l=l }
	    when Symbols.equal h (Symbols.Op Symbols.Mult) ->
	  let use_x = SX.singleton x in
	  let env =
	    List.fold_left
	      (fun env (r,_) ->
	        update_monome are_eq expl use_x env r) env l in
	  let m = mult_bornes_vars l env.monomes ty in
	  m, env
        | _ ->
	  match X.term_extract x with
	  | Some t, _ ->
	    let use_x = SX.singleton x in
	    begin
	      match Term.view t with
	      | {Term.f = (Sy.Op Sy.Div); xs = [a; b]} ->

		let pa = poly_of (fst (X.make a)) in
		let pb = poly_of (fst (X.make b)) in
		let (pa', ca, da) as npa = P.normal_form_pos pa in
		let (pb', cb, db) as npb = P.normal_form_pos pb in
		let env, ia =
		  init_alien are_eq expl pa npa ty use_x env in
		let env, ib =
		  init_alien are_eq expl pb npb ty use_x env in
		let ia, ib = match I.doesnt_contain_0 ib with
		  | Yes (ex, _) when Q.equal ca cb
		      && P.compare pa' pb' = 0 ->
		    let expl = Explanation.union ex expl in
		    I.point da ty expl, I.point db ty expl
		  | Yes (ex, _) ->
		    begin
		      match are_eq a b with
		      | Yes (ex_eq, _) ->
			let expl = Explanation.union ex expl in
			let expl = Explanation.union ex_eq expl in
			I.point Q.one ty expl,
			I.point Q.one ty expl
		      | No -> ia, ib
		    end
		  | No -> ia, ib
		in
		I.div ia ib, env
	      | _ -> I.undefined ty, env
	    end
	  | _ -> I.undefined ty, env
      in
      let u, use_x' =
        try MX.find x env.monomes
        with Not_found -> I.undefined (X.type_info x), use_x in
      let ui = I.intersect ui u in
      { env with monomes = MX.add x (ui, (SX.union use_x use_x')) env.monomes }

    let rec tighten_ac are_eq x env expl =
      let ty = X.type_info x in
      let u, use_x =
        try MX.find x env.monomes
        with Not_found -> I.undefined ty, SX.empty in
      try
        match X.ac_extract x with
	| Some {h=h;t=t;l=[x,n]}
            when Symbols.equal h (Symbols.Op Symbols.Mult) && n mod 2 = 0  ->
	  let u = I.root n u in
	  let u, use_x =
	    let (pu, use_px) =
	      try MX.find x env.monomes
	      with Not_found -> I.undefined ty, SX.empty
	    in
	    I.intersect u pu, use_px in
	  let env =
	      (* let u =  I.new_borne_inf expl Q.zero true u in *)
	    let env =
              { env with monomes = MX.add x (u, use_x) env.monomes } in
	    tighten_non_lin are_eq x use_x env expl
	  in env
	| Some {h=h;t=t;l=[x,n]} when
            Symbols.equal h (Symbols.Op Symbols.Mult) && n > 2 ->
	  let u = I.root n u in
	  let u, use_x =
	    let pu, use_px =
	      try MX.find x env.monomes
	      with Not_found -> I.undefined ty, SX.empty
	    in
	    I.intersect u pu, use_px in
	  let env = { env with monomes = MX.add x (u, use_x) env.monomes } in
	  tighten_non_lin are_eq x use_x env expl
	| _ -> env
      with Q.Not_a_float -> env


    and tighten_div x env expl =
      env

    and tighten_non_lin are_eq x use_x env expl =
      let env' = tighten_ac are_eq x env expl in
      let env' = tighten_div x env' expl in
      (*let use_x = SX.union use1_x use2_x in*)
      (* let i, _ = MX.find x env.monomes in *)
      SX.fold
        (fun x acc ->
	  let _, use = MX.find x acc.monomes in
	  (*if I.is_strict_smaller new_i i then*)
	  update_monome are_eq expl use acc x
       (*else acc*))
        use_x env'

    let update_monomes_from_poly p i polynomes monomes =
      let lp, _ = P.to_list p in
      let ty = P.type_info p in
      List.fold_left (fun monomes (a,x) ->
        let np = P.remove x p in
        let (np,c,d) = P.normal_form_pos np in
        try
	  let inp = MP.find np polynomes in
	  let new_ix =
	    I.scale
	      (Q.div Q.one a)
	      (I.add i
	         (I.scale (Q.minus d)
		    (I.add inp
		       (I.point c ty Explanation.empty)))) in
	  let old_ix, ux = MX.find x monomes in
	  let ix = I.intersect old_ix new_ix in
	  MX.add x (ix, ux) monomes
        with Not_found -> monomes)
        monomes lp

    let update_polynomes_intervals env =
      let polynomes, monomes, improved = MP.fold
        (fun p ip (polynomes, monomes, improved) ->
	  let new_i = intervals_from_monomes env p in
	  let i = I.intersect new_i ip in
	  if I.is_strict_smaller i ip then
	    let monomes = update_monomes_from_poly p i polynomes monomes in
	    MP.add p i polynomes, monomes, SP.add p improved
	  else polynomes, monomes, improved
        ) env.polynomes (env.polynomes, env.monomes, env.improved) in
      {env with polynomes = polynomes; monomes = monomes ; improved = improved}


    let find_one_eq x u =
      match I.is_point u with
      | Some (v, ex) when X.type_info x <> Ty.Tint || Q.is_int v ->
        let eq =
	  LR.mkv_eq x (alien_of (P.create [] v (X.type_info x))) in
	Some (eq, None, ex, Sig.Other)
      | _ -> None

    let find_eq eqs x u env =
      match find_one_eq x u with
      | None -> eqs
      | Some eq1 ->
	begin
          match X.ac_extract x with
	  | Some {h = h; l = [y,n]}
	      when Symbols.equal h (Symbols.Op Symbols.Mult) ->
	    let neweqs = try
		           let u, _ = MX.find y env.monomes in
		           match find_one_eq y u with
		           | None -> eq1::eqs
		           | Some eq2 -> eq1::eq2::eqs
	      with Not_found -> eq1::eqs
	    in neweqs
	  | _ -> eq1::eqs
	end

    type ineq_status =
    | Trivial_eq
    | Trivial_ineq of Q.t
    | Bottom
    | Monome of Q.t * P.r * Q.t
    | Other

    let ineq_status {Oracle.ple0 = p ; is_le = is_le} =
      match P.is_monomial p with
	Some (a, x, v) -> Monome (a, x, v)
      | None ->
	if P.is_empty p then
	  let _, v = P.separate_constant p in
	  let c = Q.sign v (* equiv. to compare v Q.zero *) in
	  if c > 0 || (c >=0 && not is_le) then Bottom
	  else
	    if c = 0 && is_le then Trivial_eq
	    else Trivial_ineq v
	else Other

    (*let ineqs_from_dep dep borne_inf is_le =
      List.map
      (fun {poly_orig = p; coef = c} ->
      let (m,v,ty) = P.mult_const minusone p in
      (* quelle valeur pour le ?????? *)
      { ple0 = {poly = (m, v +/ (Q.div borne_inf c), ty); le = is_le} ;
      dep = []}
      )dep*)

    let mk_equality p =
      let r1 = alien_of p in
      let r2 = alien_of (P.create [] Q.zero (P.type_info p)) in
      LR.mkv_eq r1 r2

    let fm_equalities env eqs rm { Oracle.ple0 = p; dep = dep; expl = ex } =
      let inqs, eqs, rm =
        MPL.fold
	  (fun a (_, p, _) (inqs, eqs, rm) ->
            MPL.remove a inqs,
            (mk_equality p, Some a, ex, Sig.Other) :: eqs,
            (LTerm a, ex) :: rm
	  ) dep (env.inequations, eqs, rm)
      in
      { env with inequations = inqs }, eqs, rm

    let update_intervals are_eq env eqs expl (a, x, v) is_le =
      let uints, use_x =
        match X.ac_extract x with
	| Some {h=h; l=l}
	    when Symbols.equal h (Symbols.Op Symbols.Mult) ->
	  let u', use_x' = MX.find x env.monomes in
	  let m = mult_bornes_vars l env.monomes (X.type_info x) in
	  I.intersect m u', use_x'
	| _ -> MX.find x env.monomes
      in
      let b = Q.div (Q.mult Q.m_one v) a in
      let u =
        if Q.sign a > 0 then
	  I.new_borne_sup expl b is_le uints
        else
	  I.new_borne_inf expl b is_le uints in
      let env = { env with monomes = MX.add x (u, use_x) env.monomes } in
      let env =  tighten_non_lin are_eq x use_x env expl in
      env, (find_eq eqs x u env)

    let update_ple0 are_eq env p0 is_le expl =
      if P.is_empty p0 then env
      else
        let ty = P.type_info p0 in
        let a, _ = P.choose p0 in
        let p, change =
	  if Q.sign a < 0 then
	    P.mult (P.create [] Q.m_one ty) p0, true
	  else p0, false in
        let p, c, _ = P.normal_form p in
        let c = Q.minus c in
        let u =
	  if change then
            I.new_borne_inf expl c is_le (I.undefined ty)
	  else
	    I.new_borne_sup expl c is_le (I.undefined ty) in
        let u, pu =
	  try
	    let pu = MP.find p env.polynomes in
	    let i = I.intersect u pu in
	    i, pu
	  with Not_found -> u, I.undefined ty
        in
        let env =
	  if I.is_strict_smaller u pu then
	    let polynomes = MP.add p u env.polynomes in
	    let monomes = update_monomes_from_poly p u polynomes env.monomes in
	    let improved = SP.add p env.improved in
	    { env with
	      polynomes = polynomes;
	      monomes = monomes;
	      improved = improved }
	  else env
        in
        match P.to_list p0 with
        | [a,x], v ->
	  fst(update_intervals are_eq env [] expl (a, x, v) is_le)
        | _ -> env

    let add_inequations are_eq acc lin =
      List.fold_left
        (fun ((env, eqs, rm) as acc) ineq ->
	  let expl = ineq.Oracle.expl in
	  match ineq_status ineq with
	  | Bottom           ->
            Debug.added_inequation "Bottom" ineq;
	    raise (Exception.Inconsistent (expl, env.classes))

	  | Trivial_eq       ->
            Debug.added_inequation "Trivial_eq" ineq;
	    fm_equalities env eqs rm ineq

	  | Trivial_ineq  c  ->
            Debug.added_inequation "Trivial_ineq"  ineq;
	    let n, pp =
	      MPL.fold
		(fun _ (_, p, is_le) ((n, pp) as acc) ->
		  if is_le then acc else
		    match pp with
		    | Some _ -> n+1, None
		    | None when n=0 -> 1, Some p
		    | _ -> n+1, None) ineq.Oracle.dep (0,None)
	    in
	    let env =
	      MPL.fold
		(fun _ (coef, p, is_le) env ->
		  let ty = P.type_info p in
		  let is_le =
		    match pp with
		      Some x -> P.compare x p = 0 | _ -> is_le && n=0
		  in
		  let p' = P.sub (P.create [] (Q.div c coef) ty) p in
		  update_ple0 are_eq env p' is_le expl
		) ineq.Oracle.dep env
	    in
	    env, eqs, rm

	  | Monome (a, x, v) ->
            Debug.added_inequation "Monome" ineq;
	    let env, eqs =
	      update_intervals
                are_eq env eqs expl (a, x, v) ineq.Oracle.is_le
	    in
	    env, eqs, rm

	  | Other            ->
	    acc


        ) acc lin

    let split_problem env ineqs =
      let current_age = Oracle.current_age () in
      let l, all_lvs =
        List.fold_left
          (fun (acc, all_lvs) ({Oracle.ple0=p} as ineq) ->


	    match ineq_status ineq with
	    | Trivial_eq | Trivial_ineq _ -> (acc, all_lvs)
	    | Bottom ->
              raise (Exception.Inconsistent (ineq.Oracle.expl, env.classes))
	    | _ ->
              let lvs =
                List.fold_left
                  (fun acc e -> SX.add e acc) SX.empty (X.leaves (alien_of p))
              in
              ([ineq], lvs) :: acc , SX.union lvs all_lvs
          )([], SX.empty) ineqs
      in
      let ll =
        SX.fold
          (fun x l ->
            let lx, l_nx = List.partition (fun (_,s) -> SX.mem x s) l in
            match lx with
            | [] -> assert false
            | e:: lx ->
              let elx =
                List.fold_left
                  (fun (l, lvs) (l', lvs') ->
                    List.rev_append l l', SX.union lvs lvs') e lx in
              elx :: l_nx
          ) all_lvs l
      in
      let ll =
        List.filter
          (fun (ineqs, _) ->
            List.exists
              (fun ineq -> Z.equal current_age ineq.Oracle.age) ineqs
          )ll
      in
      List.fast_sort (fun (a,_) (b,_) -> List.length a - List.length b) ll

    let is_normalized_poly uf p =
      let p = alien_of p in
      let rp, _  = Uf.find_r uf p in
      if X.equal p rp then true
      else begin
        fprintf fmt "%a <= 0 NOT normalized@." X.print p;
        fprintf fmt "It is equal to %a@." X.print rp;
        false
      end

    let fm uf are_eq env eqs rm  =
      Options.tool_req 4 "TR-Arith-Fm";
      let ineqs =
        MPL.fold (fun k v acc ->
          assert (is_normalized_poly uf v.Oracle.ple0);
          v::acc
        ) env.inequations []
      in
      List.fold_left
        (fun acc (ineqs, _) ->
          let mp = Oracle.MINEQS.add_to_map Oracle.MINEQS.empty ineqs in
          Oracle.available add_inequations are_eq acc mp)
        (env, eqs, rm) (split_problem env ineqs)

    let is_num r =
      let ty = X.type_info r in ty = Ty.Tint || ty = Ty.Treal

    let add_disequality are_eq env eqs p expl =
      let ty = P.type_info p in
      match P.to_list p with
      | ([], v) ->
        if Q.sign v = 0 then
          raise (Exception.Inconsistent (expl, env.classes));
	env, eqs
      | ([a, x], v) ->
	let b = Q.div (Q.minus v) a in
	let i1 = I.point b ty expl in
	let i2, use2 =
	  try
	    MX.find x env.monomes
	  with Not_found -> I.undefined ty, SX.empty
	in
	let i = I.exclude i1 i2 in
	let env ={ env with monomes = MX.add x (i,use2) env.monomes } in
	let env = tighten_non_lin are_eq x use2 env expl in
	env, find_eq eqs x i env
      | _ ->
	let a, _ = P.choose p in
	let p = if Q.sign a >= 0 then p
	  else P.mult (P.create [] Q.m_one ty) p in
	let p, c, _ = P.normal_form p in
	let i1 = I.point (Q.minus c) ty expl in
	let i2 =
	  try
	    MP.find p env.polynomes
	  with Not_found -> I.undefined ty
	in
	let i = I.exclude i1 i2 in
	let env =
	  if I.is_strict_smaller i i2 then
	    let polynomes = MP.add p i env.polynomes in
	    let monomes = update_monomes_from_poly p i polynomes env.monomes
	    in
	    let improved = SP.add p env.improved in
	    { env with
	      polynomes = polynomes;
	      monomes = monomes;
	      improved = improved}
	  else env
	in
	env, eqs

    let add_equality are_eq env eqs p expl =
      let ty = P.type_info p in
      match P.to_list p with
      | ([], v) ->
        if Q.sign v <> 0 then
	  raise (Exception.Inconsistent (expl, env.classes));
        env, eqs

      | ([a, x], v) ->
	let b = Q.div (Q.minus v) a in
	let i = I.point b ty expl in
	let i, use =
	  try
	    let i', use' = MX.find x env.monomes in
	    I.intersect i i', use'
	  with Not_found -> i, SX.empty
	in
	let env = { env with monomes = MX.add x (i, use) env.monomes} in
	let env = tighten_non_lin are_eq x use env expl in
	env, find_eq eqs x i env
      | _ ->
	let a, _ = P.choose p in
	let p = if Q.sign a >= 0 then p
	  else P.mult (P.create [] Q.m_one ty) p in
	let p, c, _ = P.normal_form p in
	let i = I.point (Q.minus c) ty expl in
	let i, ip =
	  try
	    let ip =  MP.find p env.polynomes in
	    I.intersect i ip, ip
	  with Not_found -> i, I.undefined ty
	in
	let env =
	  if I.is_strict_smaller i ip then
	    let polynomes = MP.add p i env.polynomes in
	    let monomes = update_monomes_from_poly p i polynomes env.monomes
	    in
	    let improved = SP.add p env.improved in
	    { env with
	      polynomes = polynomes;
	      monomes = monomes;
	      improved = improved }
	  else env
	in
	let env =
	  { env with
	    known_eqs = SX.add (alien_of p) env.known_eqs
          } in
	env, eqs

    let normal_form a = match a with
      | L.Builtin (false, n, [r1; r2])
          when is_le n && X.type_info r1 = Ty.Tint ->
        let pred_r1 = P.sub (poly_of r1) (P.create [] Q.one Ty.Tint) in
	LR.mkv_builtin true  n  [r2; alien_of pred_r1]

      | L.Builtin (true, n, [r1; r2]) when
	  not (is_le n) && X.type_info r1 = Ty.Tint ->
        let pred_r2 = P.sub (poly_of r2) (P.create [] Q.one Ty.Tint) in
	LR.mkv_builtin true ale [r1; alien_of pred_r2]

      | L.Builtin (false, n, [r1; r2]) when is_le n ->
	LR.mkv_builtin true alt [r2; r1]

      | L.Builtin (false, n, [r1; r2]) when is_lt n ->
	LR.mkv_builtin true ale [r2; r1]

      | _ -> a

    let remove_trivial_eqs eqs la =
      let la =
        List.fold_left (fun m ((a, _, _, _) as e) -> MR.add a e m) MR.empty la
      in
      let eqs, _ =
        List.fold_left
          (fun ((eqs, m) as acc) ((sa, root, ex, orig) as e) ->
            if MR.mem sa m then acc else e :: eqs, MR.add sa e m
          )([], la) eqs
      in
      eqs

    let equalities_from_polynomes env eqs =
      let known, eqs =
        MP.fold
          (fun p i (knw, eqs) ->
            let xp = alien_of p in
            if SX.mem xp knw then knw, eqs
            else
              match I.is_point i with
              | Some (num, ex) ->
                let r2 = alien_of (P.create [] num (P.type_info p)) in
                SX.add xp knw, (LR.mkv_eq xp r2, None, ex, Sig.Other) :: eqs
              | None -> knw, eqs
          ) env.polynomes  (env.known_eqs, eqs)
      in {env with known_eqs= known}, eqs



    let equalities_from_monomes env eqs =
      let known, eqs =
        MX.fold
          (fun x (i,_) (knw, eqs) ->
            if SX.mem x knw then knw, eqs
            else
              match I.is_point i with
              | Some (num, ex) ->
                let r2 = alien_of (P.create [] num (X.type_info x)) in
                SX.add x knw, (LR.mkv_eq x r2, None, ex, Sig.Other) :: eqs
              | None -> knw, eqs
          ) env.monomes  (env.known_eqs, eqs)
      in {env with known_eqs= known}, eqs

    let equalities_from_intervals env eqs =
      let env, eqs = equalities_from_polynomes env eqs in
      equalities_from_monomes env eqs

    let count_splits env la =
      let nb =
        List.fold_left
          (fun nb (_,_,_,i) ->
            match i with
            | CS (Th_arith, n) -> Numbers.Q.mult nb n
            | _ -> nb
          )env.size_splits la
      in
      {env with size_splits = nb}

    let assume env uf la =
      Oracle.incr_age ();
      let env = count_splits env la in
      let are_eq = Uf.are_equal uf in
      let classes = Uf.cl_extract uf in
      let env = {env with improved = SP.empty; classes = classes} in
      Debug.env env;
      let nb_num = ref 0 in
      let env, eqs, new_ineqs =
        List.fold_left
	  (fun (env, eqs, new_ineqs) (a, root, expl, _) ->
	    let a = normal_form a in
	    Debug.assume a expl;
	    try
              match a with
	      | L.Builtin(_, n, [r1;r2]) when is_le n || is_lt n ->
                incr nb_num;
                let root = match root with
	          | Some a -> a | None -> assert false in
		let p1 = poly_of r1 in
		let p2 = poly_of r2 in
		let ineq =
                  Oracle.create_ineq p1 p2 (is_le n) root expl in
		let env =
		  init_monomes_of_poly
                    are_eq env ineq.Oracle.ple0 SX.empty
                    Explanation.empty
                in
		let env =
		  update_ple0
                    are_eq env ineq.Oracle.ple0 (is_le n) expl in
		let inequations = MPL.add root ineq env.inequations in
		{env with inequations=inequations}, eqs, true

	      | L.Distinct (false, [r1; r2]) when is_num r1 && is_num r2 ->
                incr nb_num;
		let p = P.sub (poly_of r1) (poly_of r2) in
		let env = init_monomes_of_poly are_eq env p SX.empty
                  Explanation.empty
                in
		let env, eqs = add_disequality are_eq env eqs p expl in
                env, eqs, new_ineqs

	      | L.Eq(r1, r2) when is_num r1 && is_num r2 ->
                incr nb_num;
		let p = P.sub (poly_of r1) (poly_of r2) in
		let env = init_monomes_of_poly are_eq env p SX.empty
                  Explanation.empty
                in
		let env, eqs = add_equality are_eq env eqs p expl in
                env, eqs, new_ineqs

	      | _ -> (env, eqs, new_ineqs)

	    with I.NotConsistent expl ->
              Debug.inconsistent_interval expl ;
	      raise (Exception.Inconsistent (expl, env.classes))
	  )
	  (env, [], false) la

      in
      if !nb_num = 0 then env, {assume=[]; remove = []}
      else
        try
          (* we only call fm when new ineqs are assumed *)
          let env, eqs, to_remove =
            if new_ineqs then fm uf are_eq env eqs []
            else env, eqs, []
          in

          let env = update_polynomes_intervals env in
          let env, eqs = equalities_from_intervals env eqs in

          Debug.env env;
          let eqs = remove_trivial_eqs eqs la in
          Debug.implied_equalities eqs;
          let to_assume =
	    List.rev_map (fun (sa, _, ex, orig) -> (LSem sa, ex, orig)) eqs in
          env, {assume = to_assume; remove = to_remove}
        with I.NotConsistent expl ->
          Debug.inconsistent_interval expl ;
          raise (Exception.Inconsistent (expl, env.classes))


    let assume env uf la =
      let env, res = assume env uf la in
      let polys =
        MP.fold
          (fun p _ mp ->
            if Uf.is_normalized uf (alien_of p) then mp else MP.remove p mp)
          env.polynomes env.polynomes
      in
      {env with polynomes = polys}, res

    let query env uf a_ex =
      try
        ignore(assume env uf [a_ex]);
        No
      with Exception.Inconsistent (expl, classes) -> Yes (expl, classes)


    let assume env uf la =
      if Options.timers() then
        try
	  Options.exec_timer_start Timers.M_Arith Timers.F_assume;
	  let res =assume env uf la in
	  Options.exec_timer_pause Timers.M_Arith Timers.F_assume;
	  res
        with e ->
	  Options.exec_timer_pause Timers.M_Arith Timers.F_assume;
	  raise e
      else assume env uf la

    let query env uf la =
      if Options.timers() then
        try
	  Options.exec_timer_start Timers.M_Arith Timers.F_query;
	  let res = query env uf la in
	  Options.exec_timer_pause Timers.M_Arith Timers.F_query;
	  res
        with e ->
	  Options.exec_timer_pause Timers.M_Arith Timers.F_query;
	  raise e
      else query env uf la

    let case_split_polynomes env =
      let o = MP.fold
        (fun p i o ->
	  match I.finite_size i with
	  | Some s when Q.compare s Q.one > 0 ->
	    begin
	      match o with
	      | Some (s', p', _, _) when Q.compare s' s < 0 -> o
	      | _ ->
		let n, ex = I.borne_inf i in
		Some (s, p, n, ex)
	    end
	  | _ -> o
        ) env.polynomes None in
      match o with
      | Some (s, p, n, ex) ->
        let r1 = alien_of p in
	let r2 = alien_of (P.create [] n  (P.type_info p)) in
        Debug.case_split r1 r2;
	[LR.mkv_eq r1 r2, ex, CS (Th_arith, s)]
      | None ->
        Debug.no_case_split "polynomes";
	[]

    let case_split_monomes env =
      let o = MX.fold
        (fun x (i,_) o ->
	  match I.finite_size i with
	  | Some s when Q.compare s Q.one > 0 ->
	    begin
	      match o with
	      | Some (s', _, _, _) when Q.compare s' s < 0 -> o
	      | _ ->
		let n, ex = I.borne_inf i in
		Some (s, x, n, ex)
	    end
	  | _ -> o
        ) env.monomes None in
      match o with
      | Some (s,x,n,ex) ->
        let ty = X.type_info x in
        let r1 = x in
	let r2 = alien_of (P.create [] n  ty) in
        Debug.case_split r1 r2;
	[LR.mkv_eq r1 r2, ex, CS (Th_arith, s)]
      | None ->
        Debug.no_case_split "monomes";
	[]

    let check_size env res = match res with
      | [] -> res
      | [_,_, CS (Th_arith, s)] ->
        if Numbers.Q.compare (Q.mult s env.size_splits) (max_split ()) <= 0  ||
	  Numbers.Q.sign  (max_split ()) < 0 then res
        else []
      | _ -> assert false

    let case_split env uf =
      Options.tool_req 4 "TR-Arith-CaseSplit";
      match case_split_polynomes env with
      | []      -> check_size env (case_split_monomes env)
      | choices -> check_size env choices


    let add env _ = env

    let extract_improved env =
      SP.fold
        (fun p acc ->
	  MP.add p (MP.find p env.polynomes) acc)
        env.improved MP.empty


    let print_model fmt env rs = match rs with
      | [] -> ()
      | _ ->
	fprintf fmt "Relation:";
        List.iter (fun (t, r) ->
          let p = poly_of r in
          let ty = P.type_info p in
          if ty = Ty.Tint || ty = Ty.Treal then
	    let p', c, d = P.normal_form_pos p in
	    let pu' =
	      try MP.find p' env.polynomes
	      with Not_found -> I.undefined ty
	    in
	    let pm' =
	      try intervals_from_monomes ~monomes_inited:false env p'
	      with Not_found -> I.undefined ty
	    in
	    let u' = I.intersect pu' pm' in
	    if I.is_point u' = None && u' <> I.undefined ty then
	      let u =
	        I.scale d
	          (I.add u'
		     (I.point c ty Explanation.empty)) in
	      fprintf fmt "\n %a ∈ %a" Term.print t I.pretty_print u
        ) rs;
        fprintf fmt "\n@."

    let new_terms env = Term.Set.empty

  end
