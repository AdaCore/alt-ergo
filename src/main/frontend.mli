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

open Typed

module type S = sig

  type sat_env

  type output = Unsat of Explanation.t | Inconsistent
	        | Sat of sat_env | Unknown of sat_env

  val process_decl:
    (Commands.sat_tdecl -> output -> int64 -> 'a) ->
    sat_env * bool * Explanation.t -> Commands.sat_tdecl ->
    sat_env * bool * Explanation.t

  val open_file:
    Lexing.lexbuf -> in_channel ->
    ((int tdecl, int) annoted * Why_typing.env) list list

  val print_status : Commands.sat_tdecl -> output -> int64 -> unit
end

module Make (SAT: Sat_solvers.S) : S with type sat_env = SAT.t
