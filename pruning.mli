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

open Why_ptree

val split_and_prune :
  int -> (int tdecl, int) annoted list -> 
  ((int tdecl,int) annoted * bool) list list

module GF : sig
    type t
end

(* create a dependency graph from list of declaration*)
(* return (graph, goal_name, goal_formula) *)
val create_graph : (int tdecl, int) annoted list 
    -> (GF.t * string * (int tform, int) annoted)
    
(* Arguments: depth, goal_name, goal_formula, graph *)
(* return set of name of selected axioms *)
val pruning : int -> string -> (int tform, int) annoted -> GF.t 
    -> Selection.StringSet.t 

(* Arguments: list of declaration, set of axiom names *)
(* return new list of selected axioms and other declarations *)
val selected_axioms : (int tdecl, int) annoted list -> Selection.StringSet.t 
    -> ((int tdecl, int) annoted * bool) list
