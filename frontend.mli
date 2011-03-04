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

module Time : sig

  val start: unit -> unit

  val get: unit -> float

end

type output = Unsat of Explanation.t | Inconsistent | Sat | Unknown



val process_decl:
  (Why_ptree.sat_tdecl -> output -> int64 -> 'a) ->
  Sat.t * bool * Explanation.t -> Why_ptree.sat_tdecl ->
  Sat.t * bool * Explanation.t

val open_file:
  string -> Lexing.lexbuf -> 
  (Why_ptree.tdecl * Why_typing.env) list list * Smt_ast.status

val processing:
  (Why_ptree.sat_tdecl -> output -> int64 -> 'a) -> 
  (Why_ptree.tdecl * Why_typing.env) list list -> unit
