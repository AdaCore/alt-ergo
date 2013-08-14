
open Why_ptree

open Selection

(********************************** TYPE **************************************)

(* similar with record: Sat.gformula but has 1 more field: pred_def
   pred_def=true if the declaration is TPredicate(_, _, lst, _)
   and lst is not empty *)
type new_gformula = {
  new_f : Formula.t;
  new_age : int;
  new_name : Formula.t option;
  new_from_terms : Term.t list;
  new_mf : bool;
  new_gf : bool;
  new_inv : bool;
  pred_def: bool;
}

(*************************** INTERNAL MUTABLE VARIABLE ************************)

(* initial list of declaration *)
let decl_list = ref []

(* table containing all rules chosen for every step *)
(* (int, StringSet) Hashtbl.t *)
let tab_selected_rules = Hashtbl.create 15

let depth = ref 1

(*************************** INTERNAL MUTABLE VARIABLE ************************)

let sort_list lst =
  let lst = StringSet.elements lst in
  List.sort (fun x y -> if x = y then 0 else if x > y then 1 else -1) lst

(* create new structure extended from Sat.gformula *)
let create_new_gformula ff age name mf gf from_terms inv is_pred_def =
  {new_f=ff; new_age=age; new_name=name; new_mf=mf;
  new_gf=gf; new_from_terms=from_terms; new_inv = inv; pred_def = is_pred_def}

(* convert strucutre tdecl to new_gformula *)
let convert_tdecl decl =  match decl.c with
  | TAxiom(_, name, inversion, body) ->
    let ff , _ = Cnf.make_form name body in
      create_new_gformula ff 0 None true false [] inversion false
  | TGoal(_, sort, n, body) ->
    let ff, lits = Cnf.make_form "" body in
      create_new_gformula ff 0 None (sort <> Check) true [] false false
  | TPredicate_def(_, name, [], body) ->
    let ff , _ = Cnf.make_form name body in
      create_new_gformula ff 0 None true false [] false false
  | TPredicate_def(_, name, _, body) ->
    let ff , _ = Cnf.make_form name body in
      create_new_gformula ff 0 None false false [] false true
  | TFunction_def(_, name, _, _, body) ->
    let ff , _ = Cnf.make_form name body in
      create_new_gformula ff 0 None true false [] false false
  | TRewriting _ | TTypeDecl _ | TLogic _ | TInclude _  ->
    failwith "error in function convert_tdecl()"

let get_max_depth tab_selected_rules =
  Hashtbl.fold (fun depth _ max -> if depth > max then depth else max
  ) tab_selected_rules 1

(* retrieve all selected rules stored in [tab_selected_rules]
   from depth [start_depth] to depth [end_depth] and also the backup state *)
let retrieve_acc_set tab_selected_rules start_depth end_depth =
  let acc = ref StringSet.empty in
  let prev_depth = ref end_depth in
  let state = ref [] in
    while !prev_depth >= start_depth do
      if Hashtbl.mem tab_selected_rules !prev_depth then begin
        let current_set, current_state = Hashtbl.find tab_selected_rules !prev_depth in
        if !state = [] then state := [current_state];
        acc := StringSet.union current_set !acc
      end;
      prev_depth := !prev_depth - 1
    done;
    let s = match !state with | [] -> Init | s1 :: _ -> s1 in
    (!acc, s)

(* re-assign the internal depth *)
let set_depth d =
  depth := d

(* get the current internal depth *)
let get_current_depth () = !depth

let init_selection dcls =
  decl_list := dcls;
  depth := 1;
  Selection.init_selection dcls

let next_selection axioms state =
  let new_axioms, new_state = Selection.next_selection axioms state in
  if new_state = Last_Select then
    (* the last step differs for axiom selection in SAT. It selects all
       original axioms. *)
    let maximum_set = Selection.extract_rules !decl_list in
    let new_axioms = StringSet.diff maximum_set axioms in
    if StringSet.is_empty new_axioms then
      failwith "size of list cannot empty"
    else
      new_axioms, Last_Select
  else
    new_axioms, new_state

let get_init_rules () =
  let goal_set = Selection.extract_goals !decl_list in
  let new_set, new_state = next_selection goal_set Init in
  let init_set = StringSet.union goal_set new_set in
  Hashtbl.add tab_selected_rules !depth (init_set, new_state);
  depth := !depth + 1;
  if Options.debug () then begin
    Format.fprintf Options.fmt "\nDepth [%d] <select %d new rules>:@."
      (!depth - 1) (StringSet.cardinal new_set);
    if Options.verbose () then
      let sorted = sort_list new_set in
      Format.fprintf Options.fmt "New rules: [%d]\n%s@."
        (List.length sorted) (String.concat " - " sorted)
  end;
  Selection.select_rules !decl_list init_set ~include_logic_type:true

let get_new_rules () =
  let new_set =
    (* if the selection already happened at this depth, get the result from Hashtbl *)
    if Hashtbl.mem tab_selected_rules !depth then
      fst (Hashtbl.find tab_selected_rules !depth)
    else
      let max_depth = get_max_depth tab_selected_rules in
      let (_, max_state) = Hashtbl.find tab_selected_rules max_depth in
      (* nothing to select because we are already in the last step *)
      if (max_state = Last_Select) then
        StringSet.empty
      else begin
        (* first retrieve all selected rules at previous depths *)
        let (all_prev_set, prev_state) =
          retrieve_acc_set tab_selected_rules 1 (!depth - 1) in
        let new_set, new_state = next_selection all_prev_set prev_state in
        Hashtbl.add tab_selected_rules (max_depth+1) (new_set, new_state);
        new_set
      end in
  if Options.debug () then begin
    Format.fprintf Options.fmt "\nDepth [%d] <select %d new rules>:@."
      !depth (StringSet.cardinal new_set);
    if Options.verbose () then
      let sorted = sort_list new_set in
        Format.fprintf Options.fmt "New rules: [%d]\n%s@."
          (List.length sorted) (String.concat " - " sorted)
  end;
  depth := !depth + 1;
  if new_set = StringSet.empty then
    []
  else
    let selected_dcl =
      Selection.select_rules !decl_list new_set ~include_logic_type:false in
    List.map convert_tdecl selected_dcl

let get_rules_in_table ~start_depth ~end_depth =
  let (all_prev_set, _) =
    retrieve_acc_set tab_selected_rules start_depth end_depth in
  Selection.select_rules !decl_list all_prev_set ~include_logic_type:true


let tab2list table =
  Hashtbl.fold (fun k v acc -> (k, v) :: acc) table []

let print_tab_selected_rules filename =
  let oc = open_out filename in
  let fmt2 = Format.formatter_of_out_channel oc in
  let list_pair = tab2list tab_selected_rules in
  let sorted = List.sort (fun pair1 pair2 ->
      let (d1, _) = pair1 in
      let (d2, _) = pair2 in
        if d1 < d2 then
          -1
        else if d1 = d2 then
          0
        else
          1
    ) list_pair in
  let max_depth = get_max_depth tab_selected_rules in
    List.iter (fun (depth, (str_set, _)) ->
        let sorted = sort_list str_set in
        Format.fprintf fmt2 "Depth [%d/%d] (%d)@."
          depth max_depth (List.length sorted);
        Format.fprintf fmt2 "%s\n@." (String.concat " - " sorted)
      ) sorted;
    close_out oc

