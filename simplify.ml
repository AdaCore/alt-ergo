open Why_ptree

module StringSet = Selection.StringSet

type decl_list = (int tdecl, int) annoted list

(* initial list of declaration *)
let org_decl_list = ref []

let is_hypothesis name_decl = String.get name_decl 0 = '@'

(*** helper functions for simplification process ***)
let get_type sym lst_tpe old_tpe =
  try Symbols.Map.find sym lst_tpe
  with Not_found -> old_tpe

open Ty

let rec contain_polymorphic_type = function
  | Tvar{value = None} -> true
  | Tvar{value = Some t} -> contain_polymorphic_type t
  | Text(l, _) -> List.exists contain_polymorphic_type l
  | Tfarray (t1, t2) ->
    (contain_polymorphic_type t1) || (contain_polymorphic_type t2)
  | Tnext t -> contain_polymorphic_type t
  | Trecord {args=lv; lbs=lbls} ->
    (List.exists contain_polymorphic_type lv) ||
    (List.exists (fun (_, tpe) -> contain_polymorphic_type tpe) lbls)
  | _ -> false

let extract_concrete_type b =
  let rec extract b acc t =
    match t with
    | Tvar{value = Some((Text(tpe_lst, name)) as text)} -> text :: acc
    | Tvar{value = Some t} -> extract false acc t
    | Text([Text([], name)], _) | Text([], name) when b ->
        Text([], name) :: acc
    | Text(lst, _) ->
        List.fold_left (extract false) acc lst
    | Tfarray (t1, t2) ->
        extract false (extract false acc t1) t2
    | Tnext t -> extract false acc t
    | Trecord {args=lv; lbs=lbls} ->
        let acc = List.fold_left (extract false) acc lv in
        List.fold_left (fun acc (_, tp) -> extract false acc tp) acc lbls
    | _ -> acc
  in
  extract b []

let rec substitue_concrete_type tpe = function
  | Tvar{v=v1; value = Some(Tvar{value = None})} ->
      Tvar{v=v1; value = Some(tpe)}
  | Tvar{v=v1; value = Some t} ->
      Tvar{v=v1; value = Some (substitue_concrete_type tpe t)}
  | Text(lst, name) -> Text(List.map (substitue_concrete_type tpe) lst, name)
  | Tfarray (t1, t2) ->
    Tfarray (substitue_concrete_type tpe t1, substitue_concrete_type tpe t2)
  | Tnext t -> Tnext (substitue_concrete_type tpe t)
  | Trecord {args=lv; name=n; lbs=lbls} ->
    let new_args = List.map (substitue_concrete_type tpe) lv in
    let new_lbs =
      List.map (fun (hstr, t) -> (hstr, substitue_concrete_type tpe t)) lbls in
      Trecord {args=new_args; name=n; lbs=new_lbs}
  | t -> t

let extract_func_signature symbol decl_list =
  List.fold_left (fun acc decl ->
    match decl.c with
    | TLogic (_, str_lst, PFunction (arg_lst, ret_lst)) when
      List.mem symbol str_lst -> (arg_lst, ret_lst) :: acc
    | TFunction_def (_, str, arg_lst, ret_lst, _) when str = symbol ->
        (List.map snd arg_lst, ret_lst) :: acc
    | _ -> acc
  ) [] decl_list

let extract_polymorphic_type_name =
  let rec extract acc t =
    match t with
    | PPTvarid (name, _) -> StringSet.add name acc
    | PPTexternal (tpe_lst, _, _) ->
        List.fold_left extract acc tpe_lst
    | _ -> acc
  in
  extract StringSet.empty

(* example input: *)
(*    term = f(x, y, z) has signature : int -> str -> 'a list ->'a list *)
(*    substs = [x->1;y->"text", z->a] *)
(*    lst_tpe = [a: int list] *)
(* ==> new_term = f(1, "text", a) with type = int list *)
let rec transform term_annoted substs lst_tpe =
  let term = term_annoted.c in
  let {tt_ty = old_tpe; tt_desc = desc} = term in
  let newterm = match desc with
    | TTvar sym ->
        begin try (Symbols.Map.find sym substs).c
        with Not_found -> term
        end
    | TTapp (sym, lst_term) ->
      let func_name = Symbols.to_string sym in
      let new_arguments =
        List.map (fun t -> transform t substs lst_tpe) lst_term in
      let new_app = TTapp (sym, new_arguments) in
      (* at this step, we have already known all concrete type *)
      (* of every arguments [new_arguments] *)
      let func_sign_result = extract_func_signature func_name !org_decl_list in
      let newtype =
        if (List.length func_sign_result <> 0
          && contain_polymorphic_type old_tpe) then
          begin
            (* first lookup the signature of symbol [sym] *)
            (* then find the type constraint *)
            let (args_tpe_lst, ret_tpe) = List.hd func_sign_result in
            let ret_abstract_tpes = extract_polymorphic_type_name ret_tpe in
            let args_abstract_tpes =
              List.map extract_polymorphic_type_name args_tpe_lst in
            let pos_args = ref [] in
            let index = ref 0 in
              List.iter (fun tpes ->
                index := !index + 1;
                if StringSet.subset ret_abstract_tpes tpes then
                  pos_args := !pos_args @ [!index]
              ) args_abstract_tpes;
            (* next discover the concrete type *)
            (* only consider the case that we need to find only 1 concrete type *)
            let concrete_tpe = ref [] in
              index := 0;
              List.iter (fun args ->
                index := !index + 1;
                if List.length !concrete_tpe = 0 && List.mem !index !pos_args then
                begin
                  let args_tpe = args.c.tt_ty in
                  let result = extract_concrete_type true args_tpe in
                  if List.length result > 0 then
                    concrete_tpe := [List.hd result];
                end
              ) new_arguments;

              let new_tpe =
                if List.length !concrete_tpe > 0 then
                  substitue_concrete_type (List.hd !concrete_tpe) old_tpe
                else
                  old_tpe
              in
                get_type sym lst_tpe new_tpe
          end
        else
          get_type sym lst_tpe old_tpe
      in
      {tt_desc = new_app; tt_ty = newtype}
    | TTinfix (t1, sym, t2) ->
      {term with tt_desc =
        TTinfix (transform t1 substs lst_tpe, sym, transform t2 substs lst_tpe)}
    | TTprefix (sym, t) ->
      {term with tt_desc = TTprefix (sym, transform t substs lst_tpe)}
    | TTget (t1, t2) ->
      {term with tt_desc =
        TTget (transform t1 substs lst_tpe, transform t2 substs lst_tpe)}
    | TTset (t1, t2, t3) ->
      {term with tt_desc = TTset (transform t1 substs lst_tpe,
        transform t2 substs lst_tpe, transform t3 substs lst_tpe)}
    | TTextract (t1, t2, t3) ->
      {term with tt_desc = TTextract (transform t1 substs lst_tpe,
        transform t2 substs lst_tpe, transform t3 substs lst_tpe)}
    | TTconcat (t1, t2) ->
      {term with tt_desc =
        TTconcat (transform t1 substs lst_tpe,transform t2 substs lst_tpe)}
    | TTdot (t, hstr) ->
      {term with tt_desc = TTdot (transform t substs lst_tpe, hstr)}
    | TTrecord lst ->
      {term with tt_desc = TTrecord (List.map (fun (hstr, t) ->
        (hstr, transform t substs lst_tpe)) lst)}
    | TTlet (sym, t1, t2) ->
      {tt_desc =
        TTlet (sym, transform t1 substs lst_tpe, transform t2 substs lst_tpe);
       tt_ty = get_type sym lst_tpe old_tpe}
    | TTnamed (hstr, t) ->
      {term with tt_desc = TTnamed (hstr, transform t substs lst_tpe)}
    | _ -> term
  in
    {term_annoted with c = newterm}

let collect_type =
  let rec collect acc t =
    match t.c.tt_desc with
      | TTconst _ -> acc
      | TTvar sym -> Symbols.Map.add sym t.c.tt_ty acc
      | TTconcat (t1, t2) | TTget (t1, t2) | TTinfix (t1, _, t2) ->
          collect (collect acc t2) t1
      | TTprefix (_, t) -> collect acc t
      | TTapp (sym, lst_term) ->
          let acc = List.fold_left collect acc lst_term in
          Symbols.Map.add sym t.c.tt_ty acc
      | TTset (t1, t2, t3) | TTextract (t1, t2, t3) ->
          collect (collect (collect acc t3) t2) t1
      | TTdot (t, _) | TTnamed (_, t) -> collect acc t
      | TTlet (sym, t1, t2) ->
          let acc = collect (collect acc t2) t1 in
          Symbols.Map.add sym t.c.tt_ty acc
      | TTrecord lst ->
          List.fold_left (fun acc (_,t) -> collect acc t) acc lst
    in
  collect Symbols.Map.empty

(* Input: [term] = 'update(x,y,z)'; [mapping_term_lst] = [1;obj;"a"] *)
(* Output substitution: [x -> 1; y -> obj; z -> "a"] *)
let create_substitution term mapping_term_lst =
  let term_lst = match term.c.tt_desc with
    | TTapp (sym, lst) ->
      List.map (fun t ->
          match t.c.tt_desc with
          | TTvar sym -> sym
          | _ -> failwith "exception in function create_substitution()"
        ) lst
    | _ -> failwith "exception in function create_substitution()"
  in
  List.fold_left2 (fun acc sym mapping ->
    Symbols.Map.add sym mapping acc) Symbols.Map.empty term_lst
    mapping_term_lst

exception No_Match

(* comparison between 2 term, if matching return true and correspond
   substitution *)
let matching t1 t2 =
  let rec matching subst t1 t2 =
    match t1.c.tt_desc, t2.c.tt_desc with
    | TTapp (sym1, tl1), TTapp (sym2, tl2) when Symbols.equal sym1 sym2 ->
        assert (List.length tl1 = List.length tl2);
        List.fold_left2 matching subst tl1 tl2
    | TTconst const1, TTconst const2 when const1 = const2 -> subst
    | TTvar sym, _ ->
        if Symbols.Map.mem sym subst then raise No_Match
        else Symbols.Map.add sym t2 subst
    | _, _ -> raise No_Match
  in
  matching (Symbols.Map.empty) t1 t2

let contain_all_const term_lst =
  List.for_all (fun term -> match term.c.tt_desc with
    | TTconst _ -> true
    | _ -> false
    ) term_lst

let not_contain_all_const lst = not (contain_all_const lst)

(* traverse recursively through the structure of ('a tform 'a) annoted *)
let rec visit_tform process tf =
  let new_tf =
    match tf.c with
    | TFatom a -> TFatom (visit_atom process a)
    | TFop (op, tf_lst) -> TFop (op, List.map (visit_tform process) tf_lst)
    | TFforall qtf -> TFforall (visit_quantified_form process qtf)
    | TFexists qtf -> TFexists (visit_quantified_form process qtf)
    | TFlet (lst, sym, term_annoted, tf_annoted) ->
      TFlet (lst, sym, visit_term process term_annoted,
        visit_tform process tf_annoted)
    | TFnamed (name, tf_annoted) ->
      TFnamed (name, visit_tform process tf_annoted)
  in
    {tf with c = new_tf}
and visit_quantified_form process qtf =
  let {qf_triggers = trig; qf_form = tf} = qtf in
  let trigger_become_var = ref false in
  let new_trig = List.map (fun term_lst ->
      List.map (fun term ->
        let newterm = visit_term process term in
          (* should not simplify trigger-term to a constant or variable *)
          match newterm.c.tt_desc with
          | TTconst _ | TTvar _ -> trigger_become_var := true; term
          | _ -> newterm
      ) term_lst
    ) trig in
  let filter_new_trig = List.filter not_contain_all_const new_trig in
  (* if any trigger is transformed to variable, don't handle [tf] *)
  (* keep it unchanged *)
  let new_tf = if !trigger_become_var then tf else visit_tform process tf in
    {qtf with qf_triggers = filter_new_trig; qf_form = new_tf}
and visit_atom process a =
  let new_a =
    match a.c with
    | TAeq term_lst -> TAeq (List.map (visit_term process) term_lst)
    | TAdistinct term_lst -> TAdistinct (List.map (visit_term process) term_lst)
    | TAneq term_lst -> TAneq (List.map (visit_term process) term_lst)
    | TAle term_lst -> TAle (List.map (visit_term process) term_lst)
    | TAlt term_lst -> TAlt (List.map (visit_term process) term_lst)
    | TApred term -> TApred (visit_term process term)
    | TAbuilt (hstr, term_lst) ->
      TAbuilt (hstr, List.map (visit_term process) term_lst)
    | _ -> a.c
  in
    {a with c = new_a}
and visit_term process term_annoted =
  let new_term = match term_annoted.c.tt_desc with
    | TTapp _ ->
      process term_annoted
    | TTinfix (t1, sym, t2) ->
      {term_annoted.c with tt_desc =
        TTinfix (visit_term process t1, sym, visit_term process t2)}
    | TTprefix (sym, t) ->
      {term_annoted.c with tt_desc = TTprefix (sym, visit_term process t)}
    | TTget (t1, t2) ->
      {term_annoted.c with tt_desc =
        TTget (visit_term process t1, visit_term process t2)}
    | TTset (t1, t2, t3) ->
      {term_annoted.c with tt_desc = TTset (visit_term process t1,
          visit_term process t2, visit_term process t3)}
    | TTextract (t1, t2, t3) ->
      {term_annoted.c with tt_desc = TTextract (visit_term process t1,
          visit_term process t2, visit_term process t3)}
    | TTconcat (t1, t2) ->
      {term_annoted.c with tt_desc =
        TTconcat (visit_term process t1, visit_term process t2)}
    | TTdot (t, hstr) ->
      {term_annoted.c with tt_desc = TTdot (visit_term process t, hstr)}
    | TTrecord lst ->
      {term_annoted.c with tt_desc =
        TTrecord (List.map (fun (hstr, t) -> (hstr, visit_term process t)) lst)}
    | TTlet (sym, t1, t2) ->
      {term_annoted.c with tt_desc =
        TTlet (sym, visit_term process t1, visit_term process t2)}
    | TTnamed (hstr, t) ->
      {term_annoted.c with tt_desc = TTnamed (hstr, visit_term process t)}
    | _ -> term_annoted.c
  in
    {term_annoted with c = new_term}

(* replace all func symbol by its definition *)
and inline_term all_funcs term_annoted =
  let term = term_annoted.c in
  let lst_type = collect_type term_annoted in
    match term.tt_desc with
    | TTapp (sym, term_lst) ->
      let sym_str = Symbols.to_string sym in
      (* this symbol is defined by keyword "function" *)
      if Hashtbl.mem all_funcs sym_str then
        begin
          let (lhs, rhs) = Hashtbl.find all_funcs sym_str in
          let subst = create_substitution lhs term_lst in
          let new_term = transform rhs subst lst_type in
            new_term.c
        end
      else
        {term with tt_desc = TTapp (sym,
          List.map (visit_term (inline_term all_funcs)) term_lst)}
    | _ -> term

let rec find_match t tl =
  match tl with
  | [] -> raise Not_found
  | (t1,t2,_)::rest ->
      try matching t1 t, t2
      with No_Match -> find_match t rest

(* reduce long term to short term based on the [tab_mapping_term] *)
and simplify_term tab_mapping_term simplify_happened term_annoted =
  let term = term_annoted.c in
  let lst_type = collect_type term_annoted in
    match term.tt_desc with
    | TTapp (sym, term_lst) ->
        (* e.g. term_annoted = f(x1, x2, x3) and *)
        (* tab_mapping_term = [f(a,b,c) -> g(b);...] *)
        (* ==> substitution = a->x1, b->x2, c->x3 and mapping_term = g(b)*)
        (* ==> later transform this term and become final term: g(x2) *)
        begin try
          let subst, mapping_term = find_match term_annoted tab_mapping_term in
          simplify_happened := true;
          let new_term_annoted = transform mapping_term subst lst_type in
          let result_term =  {term_annoted with c = new_term_annoted.c} in
          let result_term2 =
            visit_term
            (simplify_term tab_mapping_term simplify_happened) result_term in
          result_term2.c
        with Not_found ->
            {term with tt_desc = TTapp (sym, List.map (visit_term
              (simplify_term tab_mapping_term simplify_happened)) term_lst)}
        end
    | _ -> term

(* count the depth of term *)
let rec count_term {c = {tt_desc = desc}} = match desc with
  | TTapp (_, tl) ->
      1 + List.fold_left max 0 (List.map count_term tl)
  | _ -> 0

(* extract list of function_def, it will be used for
   inlining all occurrence of function f *)
let extract_all_funcs decl_lst =
  let result = Hashtbl.create 10 in
    List.iter (fun decl -> match decl.c with
      | TFunction_def (_, name, _, _,
        {c = TFforall {qf_form = {c = TFatom {c = TAeq lst_term}}}}) ->
        let lhs = List.hd lst_term in
        let rhs = List.hd (List.tl lst_term) in
          Hashtbl.add result name (lhs, rhs)
      | _ -> ()
    ) decl_lst;
    result

(* main function for simplification
1/ firstly, transform the body of axiom into the new one by inlining all function
2/ secondly, recognize all patterns in tab_mapping_term and then reduce them *)
let simplify_axioms tab_mapping_term decl_lst =
  let all_funcs = extract_all_funcs decl_lst in

  let new_tab_mapping_term = ref tab_mapping_term in
  let simplify_decl_lst = ref [] in
  let simplify_happened = ref false in

  List.iter (fun decl -> match decl.c with
    | TAxiom (loc, name, inverse, body) ->
        let newbody = visit_tform (inline_term all_funcs) body in
        (* avoiding this case:
          [TAxiom] = [name], [forall x,y: f(x, y) = g(y)]
          [new_tab_mapping_term] = [(f(x,y) -> g(y), name),...]
      ==> [filter_mapping_term] = [ ... ] (remove mapping (_ -> _, name))
        *)
        let filter_mapping_term =
          List.filter (fun (_, _, rule) -> rule <> name) !new_tab_mapping_term in
        let simplify_body = visit_tform
          (simplify_term filter_mapping_term simplify_happened) newbody in
        let new_decl = {decl with c = TAxiom (loc, name, inverse, simplify_body)} in
        if !simplify_happened then
          begin
            if Options.debug () then
              Format.fprintf Options.fmt "Axiom simplified: %s@." name;
            simplify_happened := false;
            (* if the new simplified formula satisfy the condition *)
            (* add it to [new_tab_mapping_term] *)
            begin
              match simplify_body.c with
              | TFforall {qf_form = {c = TFatom {c = TAeq lst_term}}}
                when List.length lst_term = 2 ->
                let lhs = List.hd lst_term in
                let rhs = List.hd (List.tl lst_term) in
                if count_term lhs > count_term rhs then
                  new_tab_mapping_term :=
                    (lhs, rhs, name) :: !new_tab_mapping_term;
              | _ -> ()
            end;
            simplify_decl_lst := new_decl :: !simplify_decl_lst
          end
        else
          simplify_decl_lst := decl :: !simplify_decl_lst
    | TGoal (loc, sort, name, body) ->
        let newbody = visit_tform (inline_term all_funcs) body in
        let simplify_body = visit_tform
          (simplify_term !new_tab_mapping_term simplify_happened) newbody in
        let new_decl = {decl with c = TGoal (loc, sort, name, simplify_body)} in
          simplify_decl_lst := new_decl :: !simplify_decl_lst
    | _ -> simplify_decl_lst := decl :: !simplify_decl_lst
    ) decl_lst;
  List.rev !simplify_decl_lst, !new_tab_mapping_term

(* before simplification, extract all mapping term (t1, t2) *)
(* if there exists 1 axiom: forall... t1 = t2 and depth(t1) > depth(t2) *)
let extract_mapping_term decl_lst =
  List.fold_left (fun acc decl ->
    match decl.c with
      | TAxiom (_, name, _, {c = TFforall
      {qf_form = {c = TFatom {c = TAeq [lhs;rhs] }}}})
      when count_term lhs > count_term rhs ->
          (lhs, rhs, name) :: acc
      | _ -> acc
  ) [] decl_lst

(* simplify process *)
let simplify decl_lst =
  org_decl_list := decl_lst;
  let tab_mapping_term = extract_mapping_term decl_lst in
    fst (simplify_axioms tab_mapping_term decl_lst)

(* split the body of axioms *)
let split_conjunction_tf =
  let rec split_conjunction_tf acc tf =
    match tf.c with
    |TFop (OPand, tf_lst) ->
        List.fold_left split_conjunction_tf acc tf_lst
    | _ -> tf :: acc
  in
  split_conjunction_tf []

(* split all conjunct hypothesis into multiple hypothesis *)
let split_conjunction_in_hyps decl_list =
  List.fold_right (fun decl acc ->
    match decl.c with
    | TAxiom(loc, name, inv, body) when is_hypothesis name ->
        let lst_new_body = split_conjunction_tf body in
        if List.length lst_new_body = 1 then decl :: acc
        else begin
          let count = ref 0 in
            List.fold_left (fun acc new_body ->
              count := !count + 1;
              {decl with c =
                TAxiom(loc, name^"_"^string_of_int(!count), inv, new_body)}
              :: acc
            ) acc lst_new_body
        end
    | _ -> decl :: acc
  ) decl_list []

(* simplify and split all conjunction-hypothesis *)
let preprocessing decl_list =
  let new_decl_list = simplify (split_conjunction_in_hyps decl_list) in
    if Options.debug () then begin
      let filename = Selection.print_to_file new_decl_list ~same_order:true
          ~old_name:!Options.file ~suffix:"_simplify.why" in
      Format.fprintf Options.fmt "Printing to file: %s@." filename;
    end;
    new_decl_list
  
  