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

open Parsed
open Typed

type env

val empty_env : env

val file : bool -> env -> file ->
  ((int tdecl, int) annoted * env) list * env

val split_goals :
  ((int tdecl, int) annoted * env) list ->
  ((int tdecl, int) annoted * env) list list

val term : env -> (Symbols.t * Ty.t) list -> Parsed.lexpr ->
  (int tterm, int) annoted

val new_id : unit -> int
