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
(*     Claire Dross                                                       *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

module Make (Uf : Uf.S) (Use : Use.S with type r = Uf.R.r)
  (CC : Sig.CC with type Rel.r = Use.r
  with type 'a accumulator = 
         ('a Sig.literal * Explanation.t) list * ('a * 'a * Explanation.t) list 
  with type use = Use.t
  with type uf = Uf.t) =
struct

  module MM = Incr_match.Make (Uf) (Use)

  module RMap = struct
    include Map.Make (struct type t = Use.r let compare = Uf.R.compare end)
    let singleton r v = add r v empty
  end
  
  module KSet = Set.Make (struct
    type t = Boxed.t * Term.subst
    let compare (f1, s1) (f2, s2) =
      let c = Boxed.compare f1 f2 in
      if c = 0 then Term.compare_subst s1 s2 else c end)

    let debug = ref false

    type check = { knowns : Term.t list;
                   equalities : (Term.t * Term.t) list }

    let print_trigger =
      let rec pr_pats fmt = function
        | [] -> Format.fprintf fmt "X@."
        | [t] -> Term.print fmt t; Format.fprintf fmt "@."
        | t :: pats -> Term.print fmt t; Format.fprintf fmt ", ";
          pr_pats fmt pats in
      let rec pr_eqs fmt = function
        | [] -> Format.fprintf fmt "X@."
        | [t1, t2] -> Term.print fmt t1; Format.fprintf fmt " -> ";
          Term.print fmt t2; Format.fprintf fmt "@."
        | (t1, t2) :: pats -> Term.print fmt t1; Format.fprintf fmt " -> ";
          Term.print fmt t2; Format.fprintf fmt ", "; pr_eqs fmt pats in
      fun fmt (pats, trs) -> Format.fprintf fmt "Patterns: ";
        pr_pats fmt pats; Format.fprintf fmt "Knowns: ";
        pr_pats fmt trs.knowns; Format.fprintf fmt "Equalities: ";
        pr_eqs fmt trs.equalities

    let fresh_var, init_var =
      let c = ref 0 in
      (fun ty -> 
        let t = Term.make (Symbols.var (Format.sprintf "!x%i" !c)) [] ty in
        c := !c + 1; t),
      (fun () -> c := 0)

    type type_trig = 
      | Interp of Term.t (* interpreted term, t is a fresh variable *)
      | Pat (* uniterpreted term *)
      | Known (* ground term from the substitution *)

    (* return (top, t, pats, eqs, known), top is a type_trig and t 
       the constructed term *)
    let rec term_to_trigger vars s t (pats, eqs, knowns) =
      let { Term.f=sy; Term.xs=ts; Term.ty=ty } = Term.view t in
      match sy with
        | Symbols.Var _ ->
          if Symbols.Set.mem sy vars then
            (* Variables are ignored *) 
            (Pat, t, pats, eqs, knowns)
          else (
            if !debug then 
              (Format.fprintf Options.fmt "symbol : %a@." Symbols.print sy;
               Format.fprintf Options.fmt "subst : %a.@."
                 (fun _ -> Symbols.Map.iter (fun sy t ->
                   Format.fprintf Options.fmt "%a -> %a " Symbols.print sy
                     Term.print t)) s);
            (* Ground terms already known are into the uninterpreted part *) 
            let v = try Symbols.Map.find sy s 
              with Not_found -> assert false in
            Known, v, pats, eqs, knowns)
        | Symbols.Name _ ->
          (* Uninterpreted symbols *)
          let (ts, pats, eqs, knowns) = List.fold_right 
            (fun t (ts, pats, eqs, knowns ) ->
              let top, t, pats, eqs, knowns = 
                term_to_trigger vars s t (pats, eqs, knowns) in
              match top with
                | Interp v -> (v :: ts, pats, (v, t) :: eqs, knowns)
                | _ -> (t :: ts, pats, eqs, knowns)) 
            ts ([], pats, eqs, knowns) in
          let t = Term.make sy ts ty in
          Pat, t, pats, eqs, knowns
        | _ ->
          (* Interpreted symbols *)
          let (ts, pats, eqs, knowns) = List.fold_right
            (fun t (ts, pats, eqs, knowns) ->
              let top, t, pats, eqs, knowns = 
                term_to_trigger vars s t (pats, eqs, knowns) in
              match top with
                | Interp _ -> (t :: ts, pats, eqs, t :: knowns)
                | Pat -> (t :: ts, t :: pats, eqs, knowns)
                | Known -> (t :: ts, pats, eqs, knowns))
            ts ([], pats, eqs, knowns) in
          let t = Term.make sy ts ty in
          let v = fresh_var ty in
          Interp v, t, pats, eqs, knowns

    let term_to_trigger v s t (pats, eqs, knowns) =
      let top, t, pats, eqs, knowns = 
        term_to_trigger v s t (pats, eqs, knowns) in
      match top with
        | Interp _ -> (pats, eqs, t :: knowns)
        | Pat -> (t :: pats, eqs, knowns)
        | Known -> (pats, eqs, knowns)

    (* Cuts every term into uninterpreted parts (pats) and interpreted parts
       (knowns) linked by equalities (eqs) *)
    let term_to_trigger v s trs = 
      init_var (); 
      let (pats, eqs, knowns) = 
        List.fold_left (fun (pats, eqs, knowns) t ->
          term_to_trigger v s t (pats, eqs, knowns)) ([], [], []) trs in
      pats, { knowns = knowns; equalities = eqs }

    (* A formula without free variables can be protected by some equalities
       and some triggers. *)
    type protected_forms = 
      (Term.t * Term.t) list * Term.t list * Boxed.t * Explanation.t

    type t = { seen : KSet.t; (* Already output formulas *)
               matching : Boxed.t MM.t; (* Incremental matching environment *)
               quantifiers : (check * Symbols.Set.t) Boxed.Map.t;
               (* Quantified formulas that can be instantiated mapped to
                  the checks that has to be performed and the free variables *)
               triggers : 
                 (protected_forms list RMap.t * protected_forms list) RMap.t;
               (* {r1 -> {r2 -> forms1; ...}, forms2; ...}
                  forms1 are formulas waiting for r1 to be equal to r2
                  forms2 are formulas waiting for r1 to be known *)
               terms : (Explanation.t * Term.t * int) RMap.t;
               (* Known terms along with their explanation the round during
                  which they were produced *)
               round : int }

    type update = Uf.R.r * Uf.R.r * Explanation.t

    type witness = Term.t list * Term.subst * Explanation.t

    type trigger = Term.t list * Term.subst * Explanation.t * Boxed.t

    type quantifier = 
        Boxed.t * Symbols.Set.t * Boxed.t * Term.t list * Term.subst * 
          Explanation.t

    type env = (Uf.R.r Sig.literal * Explanation.t) list * t * CC.env

    (* Handles a protected formula. If a check is reached that is not already
       true, it is stored in triggers. *)
    let rec handle_check uf terms (acc, checks) (eqs, kns, f, ex) =
      match eqs, kns with
        | [], [] -> (f, ex) :: acc, checks
        | [], t :: kns -> (* t has to be known *)
          let r, exp = Uf.find uf t in
          let ex = Explanation.union ex exp in
          (try let exp, _, _ = RMap.find r terms in
               (* t is already known, go to the next check *)
               let ex = Explanation.union ex exp in
               handle_check uf terms (acc, checks) ([], kns, f, ex)
           with Not_found -> 
             (* t is not known, store the protected formula in triggers *)
             let v = try (let e, k = RMap.find r checks in
                          e, ([], kns, f, ex) :: k) 
               with Not_found -> RMap.empty, [[], kns, f, ex] in
             let checks = RMap.add r v checks in
             acc, checks)
        | (t1, t2) :: eqs, _ -> (* t1 has to be equal to t2 *)
          let r1, exp = Uf.find uf t1 in
          let ex = Explanation.union ex exp in
          let r2, exp = Uf.find uf t2 in
          let ex = Explanation.union ex exp in
          if r1 = r2 then 
            (* t1 is equal to t2, go to the next check *)
            handle_check uf terms (acc, checks) (eqs, kns, f, ex)
          else 
            (* t1 is not equal to t2, store the protected formula in triggers *)
            let v = (eqs, kns, f, ex) in
            let v1 = try (let e, k = RMap.find r1 checks in
                          let v = try (v :: RMap.find r2 e)
                            with Not_found -> [v] in
                          RMap.add r2 v e, k)
              with Not_found -> RMap.singleton r2 [v], [] in
            let checks = RMap.add r1 v1 checks in
            let v2 = try (let e, k = RMap.find r2 checks in
                          let v = try (v :: RMap.find r1 e)
                            with Not_found -> [v] in
                          RMap.add r1 v e, k)
              with Not_found -> RMap.singleton r1 [v], [] in
            let checks = RMap.add r2 v2 checks in
            acc, checks

    (* Handles a new known term. It is stored in terms and triggers is 
       searched for new deductions. *)
    let handle_term uf round ex t (acc, terms, checks) =
      let r, exp = Uf.find uf t in
      let ex = Explanation.union ex exp in
      if RMap.mem r terms then (acc, terms, checks)
      else
        let terms = RMap.add r (ex, t, round) terms in
        try (let eqs, trs = RMap.find r checks in
             let (acc, checks) = List.fold_left 
               (fun (acc, checks) (eqs, l, f, exp)  ->
                 let ex = Explanation.union ex exp in
                 handle_check uf terms (acc, checks) (eqs, l, f, ex)) 
               (acc, checks) trs in
             acc, terms, checks)
        with Not_found -> (acc, terms, checks)

    (* Merges two equality classes. Updates terms and triggers.
       Returns a term equal to r1 and r2 if it is known. *)
    let handle_update uf (acc, terms, checks) (r1, r2, ex) =
      (* Update of equalities in triggers *)
      let (acc, checks) = try (
        let eqs, _ = RMap.find r1 checks in
        let eqs2, trs2 = try RMap.find r2 checks
          with Not_found -> RMap.empty, [] in
        (* Moves the elements waiting for r1 to r2 *)
        let new_deductions, checks, eqs2 = 
          RMap.fold (fun r3 v (acc, checks, eqs2) ->
            if r3 = r2 then
              v :: acc, checks, eqs2
            else
              let eqs3, trs3 = RMap.find r3 checks in
              let v = List.rev_append (try RMap.find r2 eqs3
                with Not_found -> []) v in
              let checks = RMap.add r3 
                (RMap.add r2 v eqs3, trs3) checks in
              let eqs2 = RMap.add r3 v eqs2 in 
              (acc, checks, eqs2)) eqs ([], checks, eqs2) in
        (* Handles the new checks if any *)
        let checks = RMap.add r2 (eqs2, trs2) checks in
        List.fold_left (List.fold_left (handle_check uf terms))
          (acc, checks) new_deductions)
        with Not_found -> (* r1 is not awaited for any equality *)
          (acc, checks) in
      (* Update of terms and knowns in triggers *)
      try (let exp2, t2, i2 = RMap.find r2 terms in
           try (
             let exp1, t1, i1 = RMap.find r1 terms in
             (* r1 and r2 are both known, r1 and r2 in terms *)
             let terms, t = if i1 <= i2 then
                 RMap.add r2 (exp1, t1, i1) terms, t1 else terms, t2 in
             (acc, terms, checks), Some t)
           with Not_found ->
             (* r1 is not known, produce the checks waiting for it if any *)
             try (let _, trs = RMap.find r1 checks in
                  let acc, checks =
                    List.fold_left (fun (acc, checks) (eqs, l, f, exp)  ->
                      let ex = Explanation.union ex exp in
                      handle_check uf terms (acc, checks) (eqs, l, f, ex))
                      (acc, checks) trs in
                  (acc, terms, checks), Some t2)
             with Not_found -> (acc, terms, checks), Some t2
      ) with Not_found ->
        try (let exp, t, i = RMap.find r1 terms in
             (* r2 is not known, update terms and 
                produce the checks waiting for it if any *)
             let ex = Explanation.union ex exp in
             let terms = RMap.add r2 (ex, t, i) terms in
             try (let _, trs = RMap.find r2 checks in
                  let acc, checks =
                    List.fold_left (fun (acc, checks) (eqs, l, f, exp)  ->
                      let ex = Explanation.union ex exp in
                      handle_check uf terms (acc, checks) (eqs, l, f, ex))
                      (acc, checks) trs in
                  (acc, terms, checks), Some t)
             with Not_found -> (acc, terms, checks), Some t)
        with Not_found -> (acc, terms, checks), None

    (* To avoid generating infinitely many instantiations, substitutions
       are normalized so that they use the oldest known term of each equality
       class. *)
    let normalize_subst uf vars terms ((tsubst, tys), ex) =
      let (tsubst, ex) = Symbols.Set.fold (fun sy (tsubst, ex) ->
        try (let t = Symbols.Map.find sy tsubst in
             let r, _ = Uf.find uf t in
             let exp, t, r = RMap.find r terms in
             (Symbols.Map.add sy t tsubst, Explanation.union ex exp))
        with Not_found -> assert false) vars (tsubst, ex) in
      ((tsubst, tys), ex)

    let cc_add lt env t =
      CC.assume_literal env lt
        [Sig.LTerm (Literal.LT.make (Literal.Eq (t, t))), Explanation.empty]

    (* Handles new instances generated by the matching algorithm.
       insts is a list of a Incr_match.trigger_info and a substitution *)
    let handle_insts terms quants (lt, cc, seen, checks, deduced) insts =
      let (lt, cc, acc, seen) =
        List.fold_left (fun (lt, cc, acc, seen) (info, subst) ->
          if !debug && List.length subst > 0 then
            Format.fprintf Options.fmt "Form:%a@."
              Boxed.print info.Incr_match.trigger_formula;
          (* trs are the checks that must be done before deducing the instance
             and vars are the free variables of the formula *)
          let trs, vars = 
            Boxed.Map.find info.Incr_match.trigger_orig quants in
          List.fold_left (fun (lt, cc, acc, seen) (subst, ex) ->
            if KSet.mem (info.Incr_match.trigger_orig, subst) seen then
              (* The instance has already be deduced *)
              lt, cc, acc, seen
            else
              (if !debug then 
                 (Format.fprintf Options.fmt "Subst:@.";
                  Symbols.Map.iter (fun sy t -> Symbols.print Options.fmt sy;
                    Format.fprintf Options.fmt " -> "; Term.print Options.fmt t;
                    Format.fprintf Options.fmt "@.") (fst subst));
               (* update seen and compute the new check *)
               let ex = Explanation.union info.Incr_match.trigger_dep ex in
               let subst, ex = 
                 normalize_subst cc.CC.uf vars terms (subst, ex) in
               if KSet.mem (info.Incr_match.trigger_orig, subst) seen then
                 let seen = KSet.add (info.Incr_match.trigger_orig, subst) 
                   seen in
                 lt, cc, acc, seen
               else
                 let seen = KSet.add (info.Incr_match.trigger_orig, subst) 
                   seen in
                 let f = Boxed.apply_subst subst 
                   info.Incr_match.trigger_formula in
                 try(
                   let cc, kns, (lt, repr) = List.fold_left 
                     (fun (cc, l, lt) t ->
                       let t = Term.apply_subst subst t in
                       let cc, lt = cc_add lt cc t in
                       cc, t :: l, lt) (cc, [], (lt, [])) trs.knowns in
                   let cc, eqs, (lt, repr) = List.fold_left 
                     (fun (cc, l, lt) (t1, t2) ->
                       let t1 = Term.apply_subst subst t1 in
                       let cc, lt = cc_add lt cc t1 in
                       let t2 = Term.apply_subst subst t2 in
                       let cc, lt = cc_add lt cc t2 in
                       cc, (t1, t2) :: l, lt) (cc, [], (lt, repr))
                     trs.equalities in
                   assert (repr = []);
                   lt, cc, (eqs, kns, f, ex) :: acc, seen)
                 with Exception.Inconsistent _ -> assert false))
            (lt, cc, acc, seen) subst) (lt, cc, [], seen) insts in
      (* handles the deduced checks *)
      let (deduced, checks) = List.fold_left (handle_check cc.CC.uf terms)
        (deduced, checks) acc in
      (lt, cc, seen, checks, deduced)

    let empty = { seen = KSet.empty;
                  matching = MM.empty;
                  quantifiers = Boxed.Map.empty;
                  triggers = RMap.empty;
                  terms = RMap.empty;
                  round = 0 }

    let rec find_one l m =
      match l with
          [] -> Sig.No
        | (r, ex) :: l ->
          try (let ex2, _, _ = RMap.find r m in
                Sig.Yes (Explanation.union ex ex2, []))
          with Not_found -> find_one l m

    (* Determines if every subterm of t is known *)
    let is_known (lt, env, cc) (t, subst) =
      let { Term.f = s } = Term.view t in
      match s with
        | Symbols.Var _ -> Sig.Yes (Explanation.empty, [])
        | _ -> let t = Term.apply_subst subst t in
               let cc, (lt, repr) = cc_add (lt, []) cc t in
               let r, ex = Uf.find cc.CC.uf t in
               let l = List.fold_left (fun l (r1, r2, exp) ->
                 if r2 = r then (r1, Explanation.union ex exp) :: l
                 else l) [] repr in
               find_one (if l = [] then [r, ex] else l) env.terms

    (* Assumes a list of witnesses *)
    let add_witness (lt, env, cc) (l, s, dep) =
      let matching, deduced, terms, checks, insts =
        List.fold_left
          (fun (matching, deduced, terms, checks, insts) t ->
            let tv = Term.apply_subst s t in
            if !debug then (Format.fprintf Options.fmt "Term: ";
                            Term.print Options.fmt tv; 
                            Format.fprintf Options.fmt "@.");
            let matching, inst = MM.add_term dep tv matching cc.CC.uf in
            let subterms = Term.subterms Term.Set.empty t in
            let (deduced, terms, checks) = 
              Term.Set.fold (fun t -> handle_term cc.CC.uf env.round dep
                (Term.apply_subst s t)) subterms (deduced, terms, checks) in
            matching, deduced, terms, checks, inst::insts)
          (env.matching, [], env.terms, env.triggers, []) l in
      let (lt, cc, seen, checks, deduced) =
        List.fold_left (handle_insts terms env.quantifiers)
          (lt, cc, env.seen, checks, deduced) insts in
      (lt, {env with matching=matching;triggers=checks;terms=terms;seen=seen},
       cc), deduced

    (* Assumes a trigger *)
    let add_trigger (lt, env, cc) (l, s, dep, f) =
      let l = List.fold_left (Term.subterms) Term.Set.empty l in
      let l = List.map (Term.apply_subst s) (Term.Set.elements l) in
      let deduced, checks = handle_check cc.CC.uf env.terms ([], env.triggers) 
        ([], l, f, dep) in
      (lt, {env with triggers=checks}, cc), deduced

    (* Assumes a quantifier with a trigger *)
    let add_quantifier (lt, env, cc) (parent, vars, f, t, s, dep) =
      (let pats, trs = term_to_trigger vars (fst s) t in
       if !debug then 
         (Format.fprintf Options.fmt "Quantifier: "; 
          List.iter (Term.print Options.fmt) t;
          Format.fprintf Options.fmt "@."; 
          print_trigger Options.fmt (pats, trs));
       let info = { Incr_match.trigger_orig = parent;
                    Incr_match.trigger_formula = f;
                    Incr_match.trigger_dep = dep } in
       let matching, insts = MM.add_trigger info pats env.matching cc.CC.uf in
       let quants = Boxed.Map.add parent (trs, vars) env.quantifiers in
       let (lt, cc, seen, checks, deduced) =
         handle_insts env.terms quants (lt, cc, env.seen, env.triggers, [])
           insts in
       (lt, { env with matching=matching; quantifiers=quants; triggers=checks;
         seen=seen }, cc), deduced)

    (* Merges a list of equivalence classes *)
    let update (lt, env, cc) modifs =
      let matching, deduced, terms, checks, insts =
        List.fold_left 
          (fun (matching, deduced, terms, checks, insts) (r1, r2, ex) ->
            let (deduced, terms, checks), t = 
              handle_update cc.CC.uf (deduced, terms, checks) (r1, r2, ex) in
            match t with
              | None ->
                if !debug then Format.fprintf Options.fmt "Upd ignored@.";
                (matching, deduced, terms, checks, insts)
              | Some t ->
                if !debug then (Format.fprintf Options.fmt "Upd: ";
                                Term.print Options.fmt t; 
                                Format.fprintf Options.fmt "@.");
                let matching, inst = MM.merge r1 r2 t matching
                  (cc.CC.uf, cc.CC.use) in
                matching, deduced, terms, checks, inst::insts)
          (env.matching, [], env.terms, env.triggers, []) modifs in
      let (lt, cc, seen, checks, deduced) = 
        List.fold_left (handle_insts terms env.quantifiers)
        (lt, cc, env.seen, checks, deduced) insts in
      (lt, {env with matching=matching;triggers=checks;terms=terms;seen=seen;
        round=env.round+1}, cc), deduced

end
