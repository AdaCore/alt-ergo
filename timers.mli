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

type kind =
  | TNone
  | TSat
  | TMatch
  | TCC
  | TArith
  | TArrays
  | TSum
  | TRecords
  | TAc

type t

val init : unit -> t

val reset : t -> unit

val pause : t -> kind -> unit

val update : t -> kind -> unit

val pause_all : t -> unit

val start : t -> kind -> unit

val pause_and_restart : t -> kind -> (unit -> unit) -> unit

val get : t -> kind -> float
