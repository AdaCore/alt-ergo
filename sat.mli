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
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

type t

type gformula = { 
  f : Formula.t; 
  age : int; 
  name : Formula.t option; 
  from_terms : Term.t list;
  mf : bool;
  gf : bool;
  inv : bool;
}

exception Sat of t
exception Unsat of Explanation.t
exception I_dont_know of t
(* exception raised instead of Sat and I_dont_know when doing selection of
   hypotheses, in order to move to the next round of selection *)
exception More_Hypotheses of t

(* the empty sat-solver context *)
val empty : unit -> t
val empty_with_inst : (Formula.t -> unit) -> t

(* [assume env f] assume a new formula [f] in [env]. Raises Unsat if
   [f] is unsatisfiable in [env] *)
val assume : t -> gformula -> t

(* [pred_def env f] assume a new predicate definition [f] in [env]. *)
val pred_def : t -> Formula.t -> t

(* [unsat env f size] checks the unsatisfiability of [f] in
   [env]. Raises I_dont_know when the proof tree's height reaches
   [size]. Raises Sat if [f] is satisfiable in [env] *)
val unsat : t -> gformula -> Explanation.t

val print_model : header:bool -> Format.formatter -> t -> unit

val start : unit -> unit
val stop : unit -> int64

val print_sat : Format.formatter -> t -> unit

(* counting the number of instantiated axioms, *)
(* used in the function: Sat.empty_with_inst count_instantiated_axioms *)
val count_instantiated_axioms: Formula.t -> unit
val print_number_instantiated_axioms: string -> unit

(* check if we are instantiating axiom too much *)
val is_axiom_highly_instantiated: string -> bool

(* in the end of every selection step, always reset low axiom to 0*)
(* for high axiom, reset or keep depend on flag [reset_high_axiom] *)
val reset_tab_instantiated_axiom: reset_high_axiom:bool -> unit
