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

module T  : sig type t = Term.t end
module S  : sig type t = Symbols.t end
module ST : sig type elt = T.t type t = Term.Set.t end
module SA : Set.S with type elt = Literal.LT.t * Explanation.t
  
type elt = ST.t * SA.t

module type S = 
sig
  
  type t 
  type r
  val empty : t
  val find : r -> t -> elt
  val add : r -> elt -> t -> t
  val mem : r -> t -> bool
  val print : t -> unit
  val up_add : t -> ST.elt -> r -> r list -> t
      
  val congr_add : t -> r list -> ST.t
  
  val up_close_up :t -> r -> r -> t
  val congr_close_up : t -> r -> r list -> elt
end
    
module Make :
  functor (X : Sig.X) -> S with type r = X.r
