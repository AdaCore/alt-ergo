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

type 'a trigger_info = {
  trigger_orig : 'a; 
  trigger_formula : 'a ;
  trigger_dep : Explanation.t ;
}

module Make (Uf : Uf.S) (Use : Use.S with type r = Uf.R.r) :sig

  type 'a t

  type 'a result = ('a trigger_info * (Term.subst * Explanation.t) list) list

  val empty : 'a t
  val add_term : Explanation.t -> Term.t -> 'a t -> Uf.t -> 'a t
  val add_trigger : 'a trigger_info -> Term.t list -> 'a t -> Uf.t -> 'a t
  val merge : Use.r -> Use.r -> Term.t -> 'a t -> (Uf.t * Use.t) -> 'a t
  val query : Uf.t -> 'a t -> 'a t * 'a result

end
