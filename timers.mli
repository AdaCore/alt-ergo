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
  | Time_Sat
  | Time_Match
  | Time_CC
  | Time_Arith
  | Time_Arrays
  | Time_Sum
  | Time_Records
  | Time_Ac

type timer 

type t

val init : unit -> t

val pause : t -> timer -> unit

val pause_all : t -> unit

val start : t -> timer -> unit

val pause_and_restart : t -> timer -> (unit -> unit) -> unit

val get : t -> timer -> float
