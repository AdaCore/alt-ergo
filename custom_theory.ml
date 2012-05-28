let formulas = ref []

let add_theory f =
  (*List.iter (Format.fprintf Options.fmt "%a@." Formula.print) f;*)
  formulas := f

module Make (Uf : Uf.S) (Use : Use.S with type r = Uf.R.r)
  (CC : Sig.CC with type Rel.r = Use.r
  with type 'a accumulator = 
                      ('a Sig.literal * Explanation.t) list * 
                        ('a * 'a * Explanation.t) list 
  with type use = Use.t
  with type uf = Uf.t) = struct
    type use = Use.t
    type uf = Uf.t
    module I = Instantiation.Make (Uf) (Use) (CC)

    module Rel = struct
      type r = Use.r

      type choice = CLit of CC.Rel.choice | CBox of Boxed.t

      let choice_to_literal = function
        | CLit c -> CC.Rel.choice_to_literal c
        | CBox b -> Sig.LBoxed b
      let choice_mk_not = function
        | CLit c -> CLit (CC.Rel.choice_mk_not c)
        | CBox b -> CBox (Boxed.mk_not b)
      let choice_print fmt = function
        | CLit c -> CC.Rel.choice_print fmt c
        | CBox b -> Boxed.print fmt b
      let extract_terms_from_choice acc ch = 
        match ch with
        | CLit c -> CC.Rel.extract_terms_from_choice acc c
        | CBox b -> acc

      type real_env = { splits : Explanation.t Boxed.Map.t; 
                        (* Possible splits *)
                        conseq : (Boxed.t * Explanation.t) list Boxed.Map.t;
                        (* Consequences of a formula *)
                        seen : Explanation.t Boxed.Map.t; 
                        (* Formulas already assumed *)
                        inst : I.t; (* Incremental matching environment *)
                      }

      type t = CC.Rel.t * real_env option
      (* If there is no formula, the environment is None *)

      (* Give priority to other theories split *)
      let case_split (t, env) = 
        let res = match CC.Rel.case_split t, env with
          | [], Some env -> 
            (try (let b, ex = Boxed.Map.choose env.splits in
                  [CBox b, ex, Num.Int 1])
             with Not_found -> [])
          | l, _ ->  
            List.map (fun (l, ex, n) -> (CLit l, ex, n)) l in
        res

      let print_model fmt (t, _) = CC.Rel.print_model fmt t

      let query (t, _) = CC.Rel.query t

    end

    open Rel

    type env = { use : use;  
                 uf : uf ;
                 relation : Rel.t }

    type 'a accumulator = ('a Sig.literal * Explanation.t) list

    let add_conseq f v m =
      try (let l = Boxed.Map.find f m in
           Boxed.Map.add f (v :: l) m)
      with Not_found -> Boxed.Map.add f [v] m

    (* Construct a big disjunction with the triggers of an existential *)
    let mk_ors =
      let mk_eq subst t = 
        let t = Term.apply_subst subst t in
        Formula.mk_lit (Literal.LT.make (Literal.Eq (t, t))) 0 in
      let mk_and subst (trs, _) =
        let res = mk_eq subst (List.hd trs) in
        List.fold_left (fun res t ->
          let f = mk_eq subst t in
          Formula.mk_and res f 0) res (List.tl trs) in
      fun subst trs ->
        let res = mk_and subst (List.hd trs) in
        List.fold_left (fun res f ->
          let f = mk_and subst f in
          Formula.mk_or res f 0) res (List.tl trs)

    let terms_from_literal a =
      match Literal.LT.view a with 
        | Literal.Eq (t1, t2) -> [t1; t2]
        | Literal.Distinct (_, l) | Literal.Builtin (_, _, l) -> l

    let cc_add (cc, lt) t =
      CC.assume_literal cc lt
        [Sig.LTerm (Literal.LT.make (Literal.Eq (t, t))), Explanation.empty]
        
    let add_and_process a t =
      let aux a ex env = 
        let gamma, (l, rp) = CC.add env ([], []) a ex in
        CC.assume_literal gamma ([], rp) l
      in
      aux a Explanation.empty t    

    let query a t =
      try
        match Literal.LT.view a with
	  | Literal.Eq (t1, t2)  ->
	    let t, _ = add_and_process a t in
	    Uf.are_equal t.CC.uf t1 t2

	  | Literal.Distinct (false, [t1; t2]) -> 
	    let na = Literal.LT.neg a in
	    let t, _ = add_and_process na t in
	    Uf.are_distinct t.CC.uf t1 t2

	  | Literal.Distinct _ -> 
	    assert false

	  | _ -> 
	    let na = Literal.LT.neg a in
	    let t, _ = add_and_process na t in
	    let are_eq = Uf.are_equal t.CC.uf in
	    let are_neq = Uf.are_distinct t.CC.uf in
	    let class_of = Uf.class_of t.CC.uf in
	    let classes = Uf.cl_extract t.CC.uf in
	    let rna, ex_rna = CC.term_canonical_view t na Explanation.empty in
            CC.Rel.query t.CC.relation (rna, Some na, ex_rna)
	      are_eq are_neq class_of classes
      with Exception.Inconsistent (d, classes) -> 
        Sig.Yes (d, classes)

    (* Functions for boolean propagation in splits *)
    let is_true cc env (l, lv, s, p) =
      if p then query lv cc <> Sig.No &&
        try (List.iter (fun t ->
          if I.is_known ([], env.inst, cc) (t, s) = Sig.No then
            raise Not_found) (terms_from_literal l); true)
        with Not_found -> false
      else query l cc <> Sig.No

    let is_false cc env (l, lv, s, p) = 
      if p then query (Literal.LT.neg lv) cc
      else match query (Literal.LT.neg lv) cc with
        | Sig.No -> Sig.No
        | Sig.Yes (ex, _) ->
          try Sig.Yes (List.fold_left (fun ex t -> 
            match I.is_known ([], env.inst, cc) (t, s) with 
              | Sig.No -> raise Not_found
              | Sig.Yes (dep, _) -> Explanation.union ex dep)
                         ex (terms_from_literal l), [])
          with Not_found -> Sig.No

    let rec add_term (lt, env, cc, acc) (t, s, ex) =
      let ts = List.map (Term.apply_subst s) t in
      (* Add the terms to cc *)
      let cc, (lt, repr) = List.fold_left cc_add (cc, (lt, [])) ts in
      (* Update the representants in the incremental matching *)
      let (lt, inst, cc), forms = I.update (lt, env.inst, cc) repr in
      let env = { env with inst = inst } in
      (* Assume the resulting formulas *)
      let (lt, env, cc, acc) = List.fold_left assume_formula
        (lt, env, cc, acc) forms in
      (* Add the new terms to the incremental matching *)
      let (lt, inst, cc), forms = I.add_witness (lt, env.inst, cc) (t, s, ex) in
      let env = { env with inst = inst } in
      (* Assume the resulting formulas *)
      List.fold_left assume_formula (lt, env, cc, acc) forms

    and add_trigger (lt, env, cc, acc) (t, s, ex, f) =
      let ts = List.map (Term.apply_subst s) t in
      (* Add the terms to cc *)
      let cc, (lt, repr) = List.fold_left cc_add (cc, (lt, [])) ts in
      (* Update the representants in the incremental matching *)
      let (lt, inst, cc), forms = I.update (lt, env.inst, cc) repr in
      let env = { env with inst = inst } in
      (* Assume the resulting formulas *)
      let (lt, env, cc, acc) = List.fold_left assume_formula
        (lt, env, cc, acc) forms in
      (* Add the new triggers to the incremental matching *)
      let (lt, inst, cc), forms = I.add_trigger (lt, env.inst, cc)
        (t, s, ex, f) in
      let env = { env with inst = inst } in
      (* Assume the resulting formulas *)
      List.fold_left assume_formula (lt, env, cc, acc) forms

    and add_quantifier (lt, env, cc, acc) (p, vars, trs, s, f) ex =
      (* Add the new quantified formula to the incremental matching *)
      let (lt, inst, cc), forms = 
        I.add_quantifier (lt, env.inst, cc) (p, vars, f, trs, s, ex) in
      let env = { env with inst = inst } in
      (* Assume the resulting formulas *)
      List.fold_left assume_formula (lt, env, cc, acc) forms

    and assume_formula (lt, env, cc, acc) (f, ex) =
      if Boxed.Map.mem f env.seen then 
        (* f has already been assumed *)
        (lt, env, cc, acc)
      else
        try (let dep = Boxed.Map.find (Boxed.mk_not f) env.seen in
             (* not f has already been assumed *)
             raise (Exception.Inconsistent (Explanation.union dep ex, 
                                            Uf.cl_extract cc.CC.uf)))
        with Not_found ->
          (* since f with negative polarity is implied by f with positive
             polarity, we also asume f with negative polarity whenever
             f with positive polarity is assumed. *)
          let ffalse = { f with Boxed.polarity = false } in
          (* update splits *)
          let splits = Boxed.Map.remove f env.splits in
          let splits = Boxed.Map.remove (Boxed.mk_not f) splits in
          let splits = if f.Boxed.polarity then Boxed.Map.remove ffalse
              (Boxed.Map.remove (Boxed.mk_not ffalse) splits)
            else splits in
          (* update seen *)
          let seen = Boxed.Map.add f ex env.seen in
          let seen = if f.Boxed.polarity then (Boxed.Map.add ffalse ex seen)
            else seen in
          let env = { env with seen = seen; splits = splits } in
          let lt, env, cc, acc =
            match Formula.view f.Boxed.formula, Formula.view f.Boxed.view with
              | Formula.Literal l, Formula.Literal lv ->
                if f.Boxed.polarity then
                  (* The formula is a literal with a positive polarity.
                     We update the set of known terms en deduce the literal *)
                  let terms = terms_from_literal l in
                  if Options.debug_custom () then
                    Format.fprintf Options.fmt "Custom Theory deduces: %a@." 
                      Literal.LT.print lv;
                  let acc = (Sig.LTerm lv, ex) :: acc in
                  add_term (lt, env, cc, acc) (terms, f.Boxed.subst, ex)
                else 
                  (* The formula is a literal with a negative polarity.
                     We give the trigger to the instantiation module *)
                  let terms = terms_from_literal l in
                  add_trigger (lt, env, cc, acc) 
                    (terms, f.Boxed.subst, ex, {f with Boxed.polarity = true})
              | Formula.Unit (f1, f2), Formula.Unit (fv1, fv2) ->
                (* The formula is a unit, we assume both subformulas *)
                let f1 = { f with Boxed.formula = f1; view = fv1 } in
                let f2 = { f with Boxed.formula = f2; view = fv2 } in
                let acc = assume_formula (lt, env, cc, acc) (f1, ex) in
                assume_formula acc (f2, ex)
              | Formula.Clause (f1, f2), Formula.Clause (fv1, fv2) ->
                (* The formula is a clause. If one of the subformulas was
                   already assumed then we do nothing. If the negation of
                   one of the subformulas was assumed, we assume the other one.
                   In the last case, we create a split. *)
                let f1 = { f with Boxed.formula = f1; view = fv1 } in
                let f2 = { f with Boxed.formula = f2; view = fv2 } in
                if Boxed.Map.mem f1 env.seen || 
                  Boxed.Map.mem f2 env.seen
                then (lt, env, cc, acc)
                else (try (
                  let dep = 
                    Boxed.Map.find (Boxed.mk_not f1) env.seen in
                  let ex = Explanation.union dep ex in
                  assume_formula (lt, env, cc, acc) (f2, ex))
                  with Not_found ->
                    try (
                      let dep = 
                        Boxed.Map.find (Boxed.mk_not f2) env.seen in
                      let ex = Explanation.union dep ex in
                      assume_formula (lt, env, cc, acc) (f1, ex))
                    with Not_found ->
                      let splits = Boxed.Map.add f1 ex env.splits in
                      let conseq = 
                        add_conseq (Boxed.mk_not f1) (f2, ex)
                          env.conseq in
                      lt, { env with splits=splits; conseq=conseq },
                      cc, acc)
              | Formula.Lemma {Formula.qvars = vars; triggers = trs; main = ff},
                  Formula.Lemma {Formula.main = ffv} ->
                (* The formula is universally quantified.
                   We give it to the instantiation module *)
                let ff = { f with Boxed.formula = ff; view = ffv } in
                List.fold_left (fun acc (trs, _) ->
                  add_quantifier acc (f, vars, trs, f.Boxed.subst, ff) ex) 
                  (lt, env, cc, acc) trs
              | Formula.Skolem {Formula.sko_subst = f_subst; sko_f = ff},
                Formula.Skolem {Formula.sko_subst = fv_subst} ->
                (* The formula is existentially quantified.
                   We assume the presence of the subterms of one of the
                   triggers (a disjunction) and the skolemized formula. *)
                (match Formula.view (Formula.mk_not f.Boxed.view) with
                  | Formula.Lemma {Formula.qvars = vars; triggers = [trs, _];
                                   main = ffv} ->
                    let ff = { f with Boxed.formula = ff;
                      subst = fv_subst;
                      view = Formula.apply_subst fv_subst 
                        (Formula.mk_not ffv) } in
                    let new_terms = List.map (Term.apply_subst f_subst) trs in
                    let new_terms = Symbols.Set.fold (fun sy l ->
                      let t = Symbols.Map.find sy (fst f_subst) in
                      t :: l) vars new_terms in
                    let acc = add_term (lt, env, cc, acc) 
                      (new_terms, f.Boxed.subst, ex) in
                    assume_formula acc (ff, ex)
                  | Formula.Lemma {Formula.qvars = vars; triggers = trs;
                                   main = ffv} ->
                    let ff = { f with Boxed.formula = ff;
                      subst = fv_subst;
                      view = Formula.apply_subst fv_subst 
                        (Formula.mk_not ffv) } in
                    let vars = Symbols.Set.fold (fun sy l ->
                      let t = Symbols.Map.find sy (fst f_subst) in
                      t :: l) vars [] in
                    let ors = mk_ors f_subst trs in
                    let vors = mk_ors fv_subst trs in
                    let ors = { Boxed.polarity = f.Boxed.polarity;
                                view = vors; formula = ors;
                                subst = f.Boxed.subst } in
                    let acc = add_term (lt, env, cc, acc) 
                      (vars, f.Boxed.subst, ex) in
                    let acc =
                      assume_formula acc (ff, ex) in
                    assume_formula acc (ors, ex)
                  | _ -> assert false)
              | Formula.Let _, _ -> failwith "Let not implemented in theory."
              | _, _ -> assert false in
          (* deduce consequences *)
          let cons = try (Boxed.Map.find f env.conseq) with
              Not_found -> [] in
          let ffalse = { f with Boxed.polarity = false } in
          let cons = if f.Boxed.polarity then 
              try let cons = (Boxed.Map.find ffalse env.conseq)@cons in
                  cons
              with Not_found -> cons else cons in
          List.fold_left (fun acc (f, dep) ->
            let ex = Explanation.union dep ex in
            assume_formula acc (f, ex)) (lt, env, cc, acc) cons

    (* Iterates through splits to remove those that have a value *)
    let bcp (lt, env, cc, acc) =
      let splits = env.splits in
      let splits, forms = Boxed.Map.fold (fun f ex (splits, forms) ->
        match Formula.view f.Boxed.formula, Formula.view f.Boxed.view with
          | Formula.Literal l, Formula.Literal lv ->
            let v = (l, lv, f.Boxed.subst, f.Boxed.polarity) in
            (if is_true cc env v then (splits, forms)
             else match is_false cc env v with
               | Sig.Yes (ex, _) -> splits, (Boxed.mk_not f, ex) :: forms
               | Sig.No -> Boxed.Map.add f ex splits, forms) 
          | _, _ -> Boxed.Map.add f ex splits, forms)
        splits (Boxed.Map.empty, []) in
      List.fold_left assume_formula
        (lt, { env with splits=splits }, cc, acc) forms

    let assume lt env cc (f, ex) =
      let (lt, env, cc, acc) = assume_formula (lt, env, cc, []) (f, ex) in
      (lt, env, cc, acc)

    let update lt env cc acc upd = 
      let (lt, inst, cc), forms = I.update (lt, env.inst, cc) upd in
      let env = { env with inst = inst } in
      let (lt, env, cc, acc) = 
        List.fold_left assume_formula (lt, env, cc, acc)  forms in
      (lt, env, cc, acc)

    let terms_from_literal acc (a, ex) =
      match a with
        | Sig.LTerm a ->
          let l = match Literal.LT.view a with 
            | Literal.Eq (t1, t2) -> [t1; t2]
            | Literal.Distinct (_, l) | Literal.Builtin (_, _, l) -> l in
          if l = [] then acc else (l, (Symbols.Map.empty, Ty.esubst), ex)::acc
        | _ -> acc

    let rec assume_ann lt (cc, env) l =
      match l with
        | [] -> ((cc, env), lt)
        | _ ->
          let cc, (lt, repr) = CC.assume_literal cc (lt, []) l in
          let new_terms = List.fold_left terms_from_literal [] l in
          let (lt, env, cc, la) = List.fold_left
            add_term (lt, env, cc, []) new_terms in
          let (lt, env, cc, la) = update lt env cc la repr in
          assume_ann lt (cc, env) la

    let rec clean lt (cc, env) =
      let (lt, env, cc, la) = bcp (lt, env, cc, []) in
      if la = [] then ((cc, Some env), lt)
      else let ((cc, env), lt) = assume_ann lt (cc, env) la in
           clean lt (cc, env)

    (* Call bcp on env *)
    let clean lt (cc, env) =
      match env with
        | None -> (cc, env), lt
        | Some env -> clean lt (cc, env)

    (* Assumes list of literals (no box) *)
    let assume_ann lt (cc, env) l =
      match env with
        | None -> let cc, (lt, _) = CC.assume_literal cc (lt, []) l in
                  (cc, env), lt
        | Some env -> let (cc, env), lt = assume_ann lt (cc, env) l in
                       (cc, Some env), lt

    let from_env env = 
      let cc_rel, r_env = env.relation in
      let cc = { CC.relation = cc_rel; uf = env.uf; use = env.use } in
      cc, r_env

    let to_env (cc, env) =
      { relation = cc.CC.relation, env; uf = cc.CC.uf; use = cc.CC.use }

    (* Assumes a list of boxes and literals. Call bcp afterward. *)
    let assume_literal env lt l =
      let env = from_env env in
      let env, lt = List.fold_left (fun ((cc, env), lt) l ->
        match l with
        | Sig.LBoxed b, ex ->
          (match env with
            | Some env ->
              let lt, env, cc, la = assume lt env cc (b, ex) in
              assume_ann lt (cc, Some env) la
            | None -> assert false)
        | l, ex -> assume_ann lt (cc, env) [l, ex])
        (env, lt) l in
      let env, lt = clean lt env in
      to_env env, lt

    (* Environment where every formula of formulas has been assumed *)
    let empty () =
      let cc = CC.empty () in
      let lt = [] in
      let env =  { splits = Boxed.Map.empty;
                    conseq = Boxed.Map.empty;
                    seen = Boxed.Map.empty;
                    inst = I.empty } in
      let lt, env, cc, lits = List.fold_left 
        (fun acc f -> 
          let f = Boxed.from_formula f true in
          assume_formula acc (f, Explanation.empty))
        (lt, env, cc, []) !formulas in
      let env = if !formulas = [] then None
        else Some env in
      let env, _ = assume_ann lt (cc, env) lits in
      to_env env

    let add env lt a ex = 
      let cc, env = from_env env in
      let cc, (lt, repr) = CC.add cc (lt, []) a ex in
      match env with
        | None -> to_env (cc, env), lt
        | Some env ->
          let (lt, env, cc, la) = update lt env cc [] repr in
          let env, lt = assume_ann lt (cc, Some env) la in
          to_env env, lt

    let term_canonical_view env = 
      let cc, _ = from_env env in
      CC.term_canonical_view cc

  end
