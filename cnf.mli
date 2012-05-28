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

open Why_ptree

val make : ((int tdecl, int) annoted * bool) list -> sat_tdecl Queue.t

(* For the formulas of a theory. Simplify future handling by applying
   DeMorgan rules. A formula is a conjuction of disjunctions of a literal
   and a formula or a quantified formula. The order of the input is preserved.
*)
val make_theory : ((int tdecl, int) annoted * bool) list -> sat_tdecl Queue.t
