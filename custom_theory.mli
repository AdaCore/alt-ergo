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

(* Add the axiomatization *)
val add_theory : Formula.t list -> unit

module Make (Uf : Uf.S) (Use : Use.S with type r = Uf.R.r)
  (CC : Sig.CC with type Rel.r = Use.r
  with type 'a accumulator = 
                      ('a Sig.literal * Explanation.t) list * 
                        ('a * 'a * Explanation.t) list 
  with type use = Use.t
  with type uf = Uf.t): 
  Sig.CC with type Rel.r = Use.r
  with type 'a accumulator = ('a Sig.literal * Explanation.t) list 
  with type use = Use.t
  with type uf = Uf.t
