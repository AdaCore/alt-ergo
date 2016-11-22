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

type gsubst = {
  sbs : Term.t Term.Subst.t;
  sty : Ty.subst;
  gen : int ;     (* l'age d'une substitution est l'age du plus vieux
		     terme qu'elle contient *)
  goal : bool;    (* vrai si la substitution contient un terme ayant un lien
		     avec le but de la PO *)
  s_term_orig : Term.t list;
  s_lem_orig : Formula.t;
}

type trigger_info = {
  trigger : Formula.trigger;
  trigger_age : int ;  (* age d'un trigger *)
  trigger_orig : Formula.t ; (* lemme d'origine *)
  trigger_formula : Formula.t ; (* formule associee au trigger *)
  trigger_dep : Explanation.t ;
}

type term_info = {
  term_age : int ;        (* age du terme *)
  term_from_goal : bool ;   (* vrai si le terme provient du but de la PO *)
  term_from_formula : Formula.t option; (* lemme d'origine du terme *)
  term_from_terms : Term.t list;
}

type info = {
  age : int ; (* age du terme *)
  lem_orig : Formula.t list ; (* lemme d'ou provient eventuellement le terme *)
  t_orig : Term.t list;
  but : bool  (* le terme a-t-il un lien avec le but final de la PO *)
}

module type S = sig
  type t
  type theory

  val empty : t
  val add_term : term_info -> Term.t -> t -> t
  val max_term_depth : t -> int -> t
  val add_triggers : t -> (int * Explanation.t) Formula.Map.t -> t
  val terms_info : t -> info Term.Map.t
  val query : t -> theory -> (trigger_info * gsubst list) list
  val unused_context : Formula.t -> bool

end


module type Arg = sig
  type t
  val term_repr : t -> Term.t -> Term.t
  val add_term : t -> Term.t -> t
  val are_equal : t -> Term.t -> Term.t -> add_terms:bool -> Sig.answer
  val class_of : t -> Term.t -> Term.t list
end


module Make (X : Arg) : S with type theory = X.t
