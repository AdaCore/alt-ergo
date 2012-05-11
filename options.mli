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

val fmt : Format.formatter
val file : string ref
val session_file : string ref

val parse_only : bool
val type_only : bool
val stopb : int
val stepsb : int
val age_limite : int
val notriggers : bool
val debug : bool
val debug_cc : bool
val debug_use : bool
val debug_uf : bool
val debug_fm : bool
val debug_sum : bool
val debug_arith : bool
val debug_bitv : bool
val debug_ac : bool
val debug_sat : bool
val debug_sat_simple : bool
val debug_typing : bool
val debug_constr : bool
val debug_pairs : bool
val debug_arrays : bool
val debug_combine : bool
val verbose : bool
val debug_dispatch : bool
val tracefile :string
val smtfile :bool ref
val smt2file :bool ref
val satmode : bool ref
val bjmode : bool
val glouton : bool
val triggers_var : bool
val redondance : int
val astuce : bool
val select : int
val cin : in_channel
val no_rm_eq_existential : bool
val nocontracongru : bool
val arrays : bool
val pairs : bool
val term_like_pp : bool
val debug_types : bool
val all_models : bool
val model : bool
val complete_model : bool
val smt_arrays : bool
val goal_directed : bool
val bouclage : int
val max_split : Num.num
val rewriting : bool
val proof : bool
val debug_proof : bool
val rules : int
val debug_split : bool
val restricted : bool
val bottom_classes : bool

val thread_yield : (unit -> unit) ref

val profiling : bool ref
val timer_start : (Timers.kind -> unit) ref
val timer_pause : (Timers.kind -> unit) ref
