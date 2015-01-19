(******************************************************************************)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2014 --- OCamlPro                                   *)
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

module SA : Set.S with type elt = Literal.LT.t * Explanation.t
  
module type S = sig
  type t 
  type r
  val empty : t
  val find : r -> t -> Term.Set.t * SA.t
  val add : r -> Term.Set.t * SA.t -> t -> t
  val mem : r -> t -> bool
  val print : t -> unit
  val up_add : t -> Term.t -> r -> r list -> t
  val congr_add : t -> r list -> Term.Set.t
  val up_close_up :t -> r -> r -> t
  val congr_close_up : t -> r -> r list -> Term.Set.t * SA.t
end
  
module Make (X : Sig.X) : S with type r = X.r
