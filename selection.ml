
open Why_ptree

module StringSet = Set.Make(String)

type state_selection =
  | Init
  | Select_Vars
  | Select_Preds
  | Last_Select

let state2string = function
  | Init -> "Init"
  | Select_Vars -> "Select_Vars"
  | Select_Preds -> "Select_Preds"
  | Last_Select -> "Last_Select"

(* mapping (axiom_name -> pred_syms, var_syms) *)
let tab_axioms = Hashtbl.create 200

(* the mappings [tab_preds_vars] and [tab_all_def] have the same structure,
   so any query functions used for one can be used for the other *)

(* mapping (sym, axioms) of axioms where symbol sym appears *)
let tab_preds_vars = Hashtbl.create 100

(* mapping (sym, axioms) of axioms where symbol sym is defined *)
let tab_all_def = Hashtbl.create 50

(* ??? should disappear, as we cannot use it for regression testing *)
(* used for internal timeout *)
let internal_timeout = ref (-1.0)
let start_time = ref 0.0

(*** debug functions to print content of tables in files ***)

let write_to_file filename content =
  (* Write message to file *)
  let oc = open_out filename in (* create or truncate file, return channel *)
  Printf.fprintf oc "%s\n" content; (* write something *)
  close_out oc (* flush and close the channel *)

let tostring_tab1 tab1 =
  let str = ref "Table1:\n" in
  Hashtbl.iter
    (fun key (val1, val2) ->
       str := !str^key^" -> \n\tList("
       ^(String.concat "," (StringSet.elements val1))
       ^") - List("^(String.concat "," (StringSet.elements val2))^") - \n"
    ) tab1;
  !str

let tostring_tab2 tab2 =
  let str = ref "Table2:\n" in
  Hashtbl.iter
    (fun key value ->
       str := !str^key^" ->\n\tList("
       ^(String.concat "," (StringSet.elements value))^")\n"
    )
    tab2;
  !str

let debug_tab_axioms () =
  write_to_file "_tab_axioms.txt" (tostring_tab1 tab_axioms)

let debug_tab_preds_vars () =
  write_to_file "_tab_preds_vars.txt" (tostring_tab2 tab_preds_vars)

let debug_tab_def () =
  write_to_file "_tab_all_def.txt" (tostring_tab2 tab_all_def)

let print_to_file decl_list ~same_order ~old_name ~suffix =
  let filename =
    (String.sub old_name 0 (String.rindex old_name '.'))^suffix in
  let oc = open_out filename in
  let fmt = Format.formatter_of_out_channel oc in
  Pretty.print_typed_decl_list fmt ~same_order decl_list;
  close_out oc;
  filename

(*** helper functions to look up tables ***)

let get_preds_vars key = Hashtbl.find tab_axioms key

let get_axioms relation_table syms =
  StringSet.fold (fun sym acc ->
		    if Hashtbl.mem relation_table sym then
		      StringSet.union (Hashtbl.find relation_table sym) acc
		    else
		      acc
		 ) syms StringSet.empty

let get_all_preds_vars list_key =
  StringSet.fold (fun key (acc1, acc2) ->
		    let (preds, vars) = get_preds_vars key in
		    (StringSet.union preds acc1, StringSet.union vars acc2)
		 ) list_key (StringSet.empty, StringSet.empty)

(*** helper functions to create tables ***)

let rec get_free_var_term_list ~is_pred lst =
  List.fold_left
    (fun acc h -> StringSet.union (get_free_var_term ~is_pred h) acc)
    StringSet.empty lst

and get_free_var_term ~is_pred term =
  match term.c.tt_desc with
    | TTconst c -> StringSet.empty
    | TTvar sym ->
        if is_pred then
          StringSet.empty
        else
          StringSet.singleton (Symbols.to_string sym)
    | TTapp (s, term_list) ->
        if is_pred then
          StringSet.add (Symbols.to_string s)
            (get_free_var_term_list ~is_pred term_list)
        else
          get_free_var_term_list ~is_pred term_list
    | TTdot (t, _)
    | TTprefix (_, t)
    | TTnamed (_, t) ->
        get_free_var_term ~is_pred t
    | TTinfix (t1, _, t2)
    | TTget (t1, t2)
    | TTconcat (t1, t2) ->
        StringSet.union
          (get_free_var_term ~is_pred t1) (get_free_var_term ~is_pred t2)
    | TTlet (x, t1, t2) ->
        let str = Symbols.to_string x in
        let union_set = StringSet.union
          (get_free_var_term ~is_pred t1) (get_free_var_term ~is_pred t2) in
        StringSet.remove str union_set
    | TTset (t1, t2, t3)
    | TTextract (t1, t2, t3) ->
        StringSet.union (get_free_var_term ~is_pred t1)
          (StringSet.union
             (get_free_var_term ~is_pred t2) (get_free_var_term ~is_pred t3))
    | TTrecord term_list ->
        get_free_var_term_list ~is_pred (List.map snd term_list)

let get_free_var_atom ~is_pred a =
  match a.c with
    | TAtrue
    | TAfalse -> StringSet.empty
    | TAeq terms
    | TAdistinct terms
    | TAneq terms
    | TAle terms
    | TAlt terms -> get_free_var_term_list ~is_pred terms
    | TApred term -> get_free_var_term ~is_pred term
    | TAbuilt (_, _) ->
        Printf.printf "\n[get_free_var_atom] TAbuilt not implemented\n";
        StringSet.empty

let rec get_free_var_tf_list ~is_pred lst =
  List.fold_left
    (fun acc h -> StringSet.union (get_free_var_tf ~is_pred h) acc)
    StringSet.empty lst

and get_free_var_tf ~is_pred formula =
  match formula.c with
    | TFatom a -> get_free_var_atom ~is_pred a
    | TFop (_, lst_tf) -> get_free_var_tf_list ~is_pred lst_tf
    | TFforall { qf_bvars = bv; qf_upvars = uv; qf_form = tf }
    | TFexists { qf_bvars = bv; qf_upvars = uv; qf_form = tf } ->
        let free_var = get_free_var_tf ~is_pred tf in
        let closed_var = (List.map fst bv) in
        StringSet.filter
	  (fun v ->
	     not (List.exists (fun var -> Symbols.to_string var = v) 
		    closed_var))
          free_var
    | TFlet (_, _, _, _) ->
        Printf.printf "[get_free_var_tf] TFlet not implemented";
        StringSet.empty
    | TFnamed (_, _) ->
        Printf.printf "[get_free_var_tf] TFnamed not implemented";
        StringSet.empty

let get_preds_or_free_var ~is_pred decl =
  match decl.c with
    | TAxiom(_, _, _, tf)
    | TGoal(_, _, _, tf)
    | TPredicate_def(_, _, _, tf)
    | TFunction_def(_, _, _, _, tf) -> get_free_var_tf ~is_pred tf
    | _ -> StringSet.empty

let get_free_var decl = get_preds_or_free_var ~is_pred:false decl

let get_preds decl = get_preds_or_free_var ~is_pred:true decl

let add_set table lst value =
  StringSet.iter
    (fun str ->
       try
         let old_val = Hashtbl.find table str in
         Hashtbl.replace table str (StringSet.add value old_val)
       with
         | Not_found ->
             Hashtbl.add table str (StringSet.add value StringSet.empty)
    ) lst

(* create 2 type of table: *)
(*   1/ tab_axioms storing the mapping:  *)
(*      (axiom, (int tdecl, int) annoted, list sym, selected) *)
(*   2/ tab_preds_vars storing the mapping: (sym, list axiom)*)
let create_2table decl_list =
  List.iter (fun decl ->
               match decl.c with
                 | TAxiom(_, name, _, _)
                 | TGoal(_, _, name, _)
                 | TPredicate_def(_, name, _, _)
                 | TFunction_def(_, name, _, _, _) ->
                     let preds = get_preds decl in
                     let vars = get_free_var decl in
                     Hashtbl.add tab_axioms name (preds, vars);
                     add_set tab_preds_vars preds name;
                     add_set tab_preds_vars vars name
                 | _ -> ()
	    ) decl_list

(* helper functions to create table: [tab_all_def]
   LHS of equality must have the pattern:
   x = ... | f(x) = ... | f(g(...(x)...)) = ... *)
let rec is_term_belong_to_vardef term =
  match term.c.tt_desc with
    | TTvar _ -> true
    | TTapp (sym, term_lst) ->
        List.length term_lst = 1 && is_term_belong_to_vardef (List.hd term_lst)
    | _ -> false

(* collect all definition-variable having the pattern
   x = RHS && y = RHS && ... ==> return [x,y,...] *)
let rec extract_vars_def tf =
  match tf.c with
    | TFatom atom ->
        begin
          match atom.c with
            | TAeq term_list ->
                assert ((List.length term_list) = 2);
                let left_hand_side = List.hd term_list in
                let free_vars =
                  get_free_var_term ~is_pred:false left_hand_side in
                if StringSet.cardinal free_vars = 1 &&
                  is_term_belong_to_vardef left_hand_side
                then
                  free_vars
                else
                  StringSet.empty
            | _ -> StringSet.empty
        end
    | TFop (OPand, tf_lst) ->
        List.fold_left
	  (fun acc term -> StringSet.union (extract_vars_def term) acc)
	  StringSet.empty tf_lst
    | _ -> StringSet.empty

let add_def_in_table term_list axiom =
  StringSet.iter 
    (fun term ->
       if Hashtbl.mem tab_all_def term then
	 let lst = Hashtbl.find tab_all_def term in
	 Hashtbl.replace tab_all_def term (StringSet.add axiom lst)
       else
	 Hashtbl.add tab_all_def term (StringSet.singleton axiom)
    ) term_list

(* collect all definition-predicate/func symbols having the pattern
   forall x,y. f(x,y) = RHS && g(x,y) = RHS ==> return [f, g] *)
let extract_pred_def tf =
  let rec extract_pred_def_rec tf_in_forall =
    match tf_in_forall.c with
      | TFatom atom ->
          begin
            match atom.c with
              | TAeq term_list ->
                  assert ((List.length term_list) = 2);
                  let left_hand_side = List.hd term_list in
                  begin
                    match left_hand_side.c.tt_desc with
                      | TTapp (sym, _) ->
                          StringSet.singleton (Symbols.to_string sym)
                      | _ -> StringSet.empty
                  end
              | _ -> StringSet.empty
          end
      | TFop (OPand, tf_lst) when List.length tf_lst = 2 ->
          List.fold_left
      (fun acc term ->
         StringSet.union (extract_pred_def_rec term) acc) StringSet.empty tf_lst
      | _ -> StringSet.empty
  in
    match tf.c with
      | TFforall { qf_form = tf_body } -> extract_pred_def_rec tf_body
      | _ -> StringSet.empty

let get_trigger_from_axiom body = match body.c with
  | TFforall { qf_triggers = trig } | TFexists { qf_triggers = trig } ->
      Some trig
  | _ -> None

let extract_func_from_triggers trigger =
  List.fold_left
    (fun acc term_lst ->
       List.fold_left
	 (fun acc3 term ->
	    let func_name = match term.c.tt_desc with
	      | TTapp (sym, _) -> [Symbols.to_string sym]
	      | _ -> []
	    in
	    if List.length func_name > 0 then
	      StringSet.add (List.hd func_name) acc
	    else
	      acc
	 ) acc term_lst
    ) StringSet.empty trigger

(* create table storing the definition of symbol (pred/var) *)
let extract_all_def decl_list =
  List.iter
    (fun decl ->
       match decl.c with
	 | TAxiom (_, name, _, body) ->
	     (* recognize axioms that define variables *)
	     let var_def = extract_vars_def body in
	     add_def_in_table var_def name;

	     (* recognize axioms that define predicates/functions *)
	     let pred_def = extract_pred_def body in
	     add_def_in_table pred_def name;

	     (* axioms that define predicates cannot be recognized right now, 
		when they are under the form p(...) <-> def, because Why3 
		rewrites the equivalence operator into a conjunction of
		implication. So recognize it specially based on triggers that
		are generated by GNATprove in that case. *)
	     let starts_with str p =
	       let len = String.length p in
	       if String.length str < len then
		 false
	       else
		 String.sub str 0 len = p
	     in
	     let check_sub_str s1 s2 =
	       try
		 let len = String.length s2 in
		 for i = 0 to String.length s1 - len do
		   if String.sub s1 i len = s2 then raise Exit
		 done;
		 false
	       with Exit -> true
	     in
	     if starts_with name "def_axiom" || check_sub_str name "_def" then
	       begin
		 let triggers = get_trigger_from_axiom body in
		 match triggers with
		   | Some trig ->
		       let func_names = extract_func_from_triggers trig in
		       add_def_in_table func_names name
		   | None -> ()
	       end
	 | TPredicate_def (_, s, _, _) | TFunction_def (_, s, _, _, _) ->
	     add_def_in_table (StringSet.singleton s) s
	 | _ -> ()
    ) decl_list

(* return the list of declarations from [decls] which have names in 
   [name_of_selected_rules] *)
let select_rules decls name_of_selected_rules ~include_logic_type =
  List.filter
    (fun decl -> match decl.c with
       | TAxiom (_, name, _, _)
       | TPredicate_def (_, name, _, _)
       | TFunction_def (_, name, _, _, _)
       | TGoal (_, _, name, _) -> StringSet.mem name name_of_selected_rules
       | _ -> include_logic_type
    ) decls

(* return the names of all declarations from [decls] *)
let extract_rules decls =
  List.fold_left
    (fun acc decl -> match decl.c with
       | TAxiom (_, name, _, _)
       | TGoal (_, _, name, _)
       | TPredicate_def (_, name, _, _)
       | TFunction_def (_, name, _, _, _) -> StringSet.add name acc
       | _ -> acc
    ) StringSet.empty decls

(* select all rules which contain no pred/var symbols *)
let select_arith_axioms () =
  Hashtbl.fold
    (fun key (preds, vars) acc ->
       if StringSet.is_empty preds && StringSet.is_empty vars then
	 StringSet.add key acc
       else
	 acc
    ) tab_axioms StringSet.empty

(*** helper functions for axiom selection process ***)

(* select recursively from [axioms] other axioms that share at least one symbol
   with the previously selected axioms. [relation_table] stores the relation
   from symbols to axioms, which may represent either definition axioms only or
   all axioms. [select_preds] is true if the selection is based on
   predicate/function symbols. [select_vars] is true if the selection is based
   on variable symbols. [axioms] is a subset of the set returned. *)
let select_all_related
    ?(select_preds=false) ?(select_vars=false) relation_table axioms =
  let rec select_next acc axioms =
    if StringSet.is_empty axioms then
      acc
    else
      let (preds, vars) = get_all_preds_vars axioms in
      let syms =
        if select_preds && select_vars then
          StringSet.union preds vars
        else if select_preds then
          preds
        else if select_vars then
          vars
        else
          StringSet.empty
      in
      let new_axioms = get_axioms relation_table syms in
      let prev_axioms = StringSet.union axioms acc in
      select_next prev_axioms (StringSet.diff new_axioms prev_axioms)
  in
  select_next StringSet.empty axioms

(* select recursively all definition axioms related to [axioms] by symbol
   sharing. [axioms] is a subset of the set returned. *)
let select_all_def axioms =
  select_all_related ~select_preds:true ~select_vars:true tab_all_def axioms

(* select all axioms directly sharing a variable symbol with [axioms].
   [axioms] is a subset of the set returned. *)
let select_direct_related_vars axioms =
  let (_, vars) = get_all_preds_vars axioms in
  let new_axioms = get_axioms tab_preds_vars vars in
  StringSet.union axioms new_axioms

(* select all axioms directly sharing a predicate/function symbol with [axioms].
   [axioms] is a subset of the set returned. *)
let select_direct_related_preds axioms =
  let (preds, _) = get_all_preds_vars axioms in
  (* ??? The following kludge should be removed. There should be axioms
     relating div and mod, and that should be sufficient. *)
  (* 'div' and 'mod' axioms should be select together *)
  let new_preds =
    if StringSet.mem "div" preds || StringSet.mem "mod" preds then
      begin
        let div_flag = Hashtbl.mem tab_preds_vars "div" in
        let mod_flag = Hashtbl.mem tab_preds_vars "mod" in
        if div_flag && mod_flag then 
	  StringSet.add "div" (StringSet.add "mod" preds)
        else if div_flag then StringSet.add "div" preds
        else if mod_flag then StringSet.add "div" preds
        else preds
      end
    else preds in
  let new_axioms = get_axioms tab_preds_vars new_preds in
  StringSet.union axioms new_axioms

(* retrieve all selected axioms stored in [tab_selected_rules]
   from depth [start_depth] to depth [end_depth] *)
let retrieve_acc_set tab_selected_rules start_depth end_depth =
  let acc = ref StringSet.empty in
  let prev_depth = ref end_depth in
  while !prev_depth >= start_depth do
    if Hashtbl.mem tab_selected_rules !prev_depth then
      acc := StringSet.union (Hashtbl.find tab_selected_rules !prev_depth) !acc;
    prev_depth := !prev_depth - 1
  done;
  !acc

let extract_goals decls =
  List.fold_left (fun acc decl -> match decl.c with
		    | TGoal (_, _, name, _) -> StringSet.add name acc
		    | _ -> acc
		 ) StringSet.empty decls

let init_selection decls =
  Hashtbl.clear tab_axioms;
  Hashtbl.clear tab_preds_vars;
  Hashtbl.clear tab_all_def;
  extract_all_def decls;
  create_2table decls

(* main function for selection process *)
let rec next_selection axioms state =
  let new_axioms, new_state = match state with
    | Init ->
        (* start with selecting all defining axioms from [axioms], plus
           arithmetic axioms that would otherwise never be selected *)
        let new_axioms = select_all_def axioms in
        let arith_set = select_arith_axioms () in
        let new_axioms = StringSet.union new_axioms arith_set in
        (new_axioms, Select_Vars)

    | Select_Vars ->
        (* next, select axioms that directly share a variable symbol with
           [axioms], and close this set by all defining axioms. If no new
           axioms are found this way, move to the next step. *)
        let new_axioms = select_direct_related_vars axioms in
        let new_axioms = select_all_def new_axioms in
        if StringSet.equal new_axioms axioms then
          next_selection new_axioms Select_Preds
        else
          (new_axioms, Select_Vars)

    | Select_Preds ->
        (* start this step by selecting based on variable sharing like
           previously, as the newly generated axioms may involve new
           variables *)
        let new_axioms = select_direct_related_vars axioms in
        (* next, select axioms that directly share a predicate/function symbol
           with [new_axioms], and close this set by all defining axioms. If no
           new axioms are found this way, move to the next step. *)
        let new_axioms = select_direct_related_preds new_axioms in
        let new_axioms = select_all_def new_axioms in
        if StringSet.equal new_axioms axioms then
          (new_axioms, Last_Select)
        else
          (new_axioms, Select_Preds)

    | Last_Select ->
        failwith "[next_selection] Last_Select is not a valid state"
  in
  StringSet.diff new_axioms axioms, new_state

(*** timeout function ***)

let set_internal_timeout timeout =
  internal_timeout := timeout

let start_timer () =
  start_time := (Unix.times ()).Unix.tms_utime

let check_timeout () =
  if !internal_timeout = -1.0 then
    false
  else
    begin
      let current = (Unix.times ()).Unix.tms_utime in
      if current -. !start_time > !internal_timeout then
        true
      else
        false
    end
