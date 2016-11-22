(******************************************************************************)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2015 --- OCamlPro                                   *)
(*     This file is distributed under the terms of the CeCILL-C licence       *)
(******************************************************************************)

(******************************************************************************)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*   This file is distributed under the terms of the CeCILL-C licence         *)
(******************************************************************************)

module type S = sig
  type t
  type tbox
  type instances = (Formula.gformula * Explanation.t) list

  val empty : t
  val add_terms : t -> Term.Set.t -> Formula.gformula -> t
  val add_lemma : t -> Formula.gformula -> Explanation.t -> t * instances
  val add_predicate : t -> Formula.gformula -> t

  val m_lemmas :
    t ->
    tbox ->
    (Formula.t -> Formula.t -> bool) ->
    int ->
    instances * instances (* goal_directed, others *)

  val m_predicates :
    t ->
    tbox ->
    (Formula.t -> Formula.t -> bool) ->
    int ->
    instances * instances (* goal_directed, others *)

  (* returns used axioms/predicates * unused axioms/predicates *)
  val retrieve_used_context :
    t -> Explanation.t -> Formula.t list * Formula.t list

  val register_max_term_depth : t -> int -> t

end

module Make (X : Theory.S) : S with type tbox = X.t
