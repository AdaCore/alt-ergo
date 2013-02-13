
open Why_ptree

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

(* [init decls filename] do an initial step before starting selection *)
val init_selection: (int tdecl, int) annoted list -> unit

(* set and retrieve the internal depth *)
val set_depth: int -> unit
val get_current_depth: unit -> int

(* get the initial rules *)
val get_init_rules: unit -> (int tdecl, int) annoted list

(* get new rules at certain depth *)
val get_new_rules: unit -> new_gformula list

val get_rules_in_table: start_depth:int -> end_depth:int
    -> (int tdecl, int) annoted list

val print_tab_selected_rules: string -> unit


