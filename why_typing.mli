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

type env

val file : Why_ptree.file -> (int Why_ptree.tdecl * env) list 

val split_goals : 
  (int Why_ptree.tdecl * env) list -> (int Why_ptree.tdecl * env) list list

val term : env -> (Symbols.t * Ty.t) list -> Why_ptree.lexpr -> int Why_ptree.tterm


