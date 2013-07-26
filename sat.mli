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

(* the empty sat-solver context *)
val empty : unit -> t
val empty_with_inst : (Formula.t -> unit) -> t

(* [assume env f] assume a new formula [f] in [env]. Raises Unsat if
   [f] is unsatisfiable in [env] *)
val assume : t -> gformula -> t

(* [add_theory env fs] assume a new custom theory [fs] in [env]. Raises Unsat if
   [fs] is unsatisfiable in [env] *)
val add_theory : t -> Formula.t list -> t

(* [pred_def env f] assume a new predicate definition [f] in [env]. *)
val pred_def : t -> Formula.t -> t

(* [unsat env f size] checks the unsatisfiability of [f] in
   [env]. Raises I_dont_know when the proof tree's height reaches
   [size]. Raises Sat if [f] is satisfiable in [env] *)
val unsat : t -> gformula -> Explanation.t

val print_model : header:bool -> Format.formatter -> t -> unit

val start : unit -> unit
val stop : unit -> int64
