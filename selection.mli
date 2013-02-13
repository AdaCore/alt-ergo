
open Why_ptree

module StringSet : Set.S with type elt = String.t

type state_selection =
  | Init
  | Select_Vars
  | Select_Preds
  | Last_Select

val state2string: state_selection -> string

(* return name of goals in the list of declarations *)
val extract_goals: (int tdecl, int) annoted list -> StringSet.t

(* initialize global mappings with the given list of declarations *)
val init_selection: (int tdecl, int) annoted list -> unit

(* given a set of selected axioms, and a state, return the set of
   newly selected axioms (not overlapping with the first one), and a
   new state *)
val next_selection: 
  StringSet.t -> state_selection -> StringSet.t * state_selection

(* [select_rules decls names include_logic_type] return the list of 
   declarations from [decls] which have names in the set [names].
   If [include_logic_type] is true then select all logic/type rules. *)
val select_rules: (int tdecl, int) annoted list ->
  StringSet.t -> include_logic_type:bool -> (int tdecl, int) annoted list

(* [extract_rules decls] return the names of all declarations from [decls] *)
val extract_rules: (int tdecl, int) annoted list -> StringSet.t

(* function for InternalTimeout *)
val internal_timeout : float ref
val set_internal_timeout: float -> unit
val start_timer: unit -> unit
val check_timeout: unit -> bool

(* function for debugging *)
val print_to_file :
  (int tdecl, int) annoted list -> same_order:bool 
      -> old_name:string -> suffix:string -> string
