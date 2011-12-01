(**************************************************************************)
(*                                                                        *)
(*     The Alt-ergo theorem prover                                        *)
(*     Copyright (C) 2006-2011                                            *)
(*                                                                        *)
(*     Sylvain Conchon                                                    *)
(*     Evelyne Contejean                                                  *)
(*                                                                        *)
(*     Francois Bobot                                                     *)
(*     Stephane Lescuyer                                                  *)
(*     Mohamed Iguernelala                                                *)
(*     Alain Mebsout                                                      *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

open Why_annoted


val toggle_prune_nodep : 'a annoted -> GText.tag -> unit

val connect : env -> unit

val clear_used_lemmas_tags : env -> unit

val show_used_lemmas : env -> Explanation.t -> unit

val prune_unused : env -> unit
