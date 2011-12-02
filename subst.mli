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

type +'a t = 'a Symbols.Map.t

module type PRINT_TYPE = sig
  type t
  val print : Format.formatter -> t -> unit
end

module type S = sig
  type elt

  include Map.S with type key = Symbols.t and type 'a t = 'a t

  val print : Format.formatter -> elt t -> unit
end

module Make (X : PRINT_TYPE) : S with type elt = X.t


