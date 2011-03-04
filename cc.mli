(**************************************************************************)
(*                                                                        *)
(*     The Alt-ergo theorem prover                                        *)
(*     Copyright (C) 2006-2010                                            *)
(*                                                                        *)
(*     Sylvain Conchon                                                    *)
(*     Evelyne Contejean                                                  *)
(*     Stephane Lescuyer                                                  *)
(*     Mohamed Iguernelala                                                *)
(*     Alain Mebsout                                                      *)
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
(*  val add : Literal.LT.t -> Explanation.t -> t -> t*)
  val assume : Literal.LT.t -> Explanation.t -> t -> t * int
  val query : Literal.LT.t -> t -> Explanation.t option
  val class_of : t -> Term.t -> Term.t list
  val explain : Literal.LT.t -> t -> Explanation.t
  val extract_model : t -> Literal.LT.t list * Literal.LT.t list
  val rewrite_system : t -> (Term.t Why_ptree.rwt_rule) list -> t
end

module Make (X:Sig.X) : S
