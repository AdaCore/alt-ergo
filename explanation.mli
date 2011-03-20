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

type t

val everything : t

val empty : t

val mem : Formula.t -> t -> bool

val singleton : ?bj:bool -> Formula.t -> t

val make_deps : Formula.Set.t -> t

val union : t -> t -> t

val merge : t -> t -> t

val remove : Formula.t -> t -> t

val print : Format.formatter -> t -> unit

val print_proof : Format.formatter -> t -> unit

val ids_of : t -> int list option

val formulas_of : t -> Formula.Set.t
