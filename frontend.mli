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

open Why_ptree

module Time : sig

  val start : unit -> unit
  val get : unit -> float

  val set_timeout : unit -> unit
  val unset_timeout : unit -> unit

end

type output = Unsat of Explanation.t | Inconsistent 
	      | Sat of Sat.t | Unknown of Sat.t


val process_decl:
  (Why_ptree.sat_tdecl -> output -> int64 -> 'a) ->
  Sat.t * bool * Explanation.t -> sat_tdecl ->
  Sat.t * bool * Explanation.t

val open_file:
  string -> Lexing.lexbuf -> 
  ((int tdecl, int) annoted * Why_typing.env) list list * Smt_ast.status

val processing:
  (Why_ptree.sat_tdecl -> output -> int64 -> 'a) -> 
  ((int tdecl, int) annoted * Why_typing.env) list list -> unit


val print_status : sat_tdecl -> output -> int64 -> unit

val main : unit -> unit
