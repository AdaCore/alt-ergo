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

open Format
open Options
open Sig
open Exception

module type S = sig

  type t
  type r = Combine.Shostak.r

  val empty : unit -> t

  val empty_facts : unit -> r Sig.facts

  val add_fact : r Sig.facts -> r fact -> unit

  val add_term :
    t ->
    r Sig.facts -> (* acc *)
    Term.t ->
    Explanation.t ->
    t * r Sig.facts

  val add :
    t ->
    r Sig.facts -> (* acc *)
    Literal.LT.t ->
    Explanation.t -> t * r Sig.facts

  val assume_literals :
    t ->
    (r Sig.literal * Explanation.t * Sig.lit_origin) list ->
    r Sig.facts ->
    t * (r Sig.literal * Explanation.t * Sig.lit_origin) list

  val case_split : t -> (r Literal.view * Explanation.t * Sig.lit_origin) list
  val query :  t -> Literal.LT.t -> Sig.answer
  val new_terms : t -> Term.Set.t
  val class_of : t -> Term.t -> Term.t list
  val are_equal : t -> Term.t -> Term.t -> Sig.answer
  val are_distinct : t -> Term.t -> Term.t -> Sig.answer
  val cl_extract : t -> Term.Set.t list
  val term_repr : t -> Term.t -> Term.t
  val print_model : Format.formatter -> t -> unit

end

module Main : S
