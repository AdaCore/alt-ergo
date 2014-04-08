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
(*     Claire Dross                                                       *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(* Persistent and incremental congruence-closure modulo X data structure. 

   This module implements the CC(X) algorithm.

*)

module type S = sig
  type t

  val empty : unit -> t
  val assume : Literal.LT.t -> Explanation.t -> t -> t * Term.Set.t
  val query : Literal.LT.t -> t -> Sig.answer
  val query_with_splits : Literal.LT.t -> t -> Sig.answer
  val class_of : t -> Term.t -> Term.t list
  val class_of_with_splits : t -> Term.t -> Term.t list
  val print_model : Format.formatter -> t -> unit
  val cl_extract : t -> Term.Set.t list
  val term_repr : t -> Term.t -> Term.t
  val add_theory : t -> Formula.t list -> t * Term.Set.t
end

module Make (X:Sig.X) : S
