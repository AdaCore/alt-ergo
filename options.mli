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

val fmt : Format.formatter
val file : string ref
val session_file : string ref

val parse_only : unit -> bool
val type_only : unit -> bool
val stopb : unit -> int
val stepsb : unit -> int
val age_limite : unit -> int
val notriggers : unit -> bool
val debug : unit -> bool
val debug_cc : unit -> bool
val debug_use : unit -> bool
val debug_uf : unit -> bool
val debug_fm : unit -> bool
val debug_sum : unit -> bool
val debug_arith : unit -> bool
val debug_bitv : unit -> bool
val debug_ac : unit -> bool
val debug_sat : unit -> bool
val debug_sat_simple : unit -> bool
val debug_typing : unit -> bool
val debug_constr : unit -> bool
val debug_pairs : unit -> bool
val debug_arrays : unit -> bool
val debug_combine : unit -> bool
val verbose : unit -> bool
val debug_dispatch : unit -> bool
val tracefile : unit -> string
val smtfile :bool ref
val smt2file :bool ref
val satmode : bool ref
val bjmode : unit -> bool
val glouton : unit -> bool
val triggers_var : unit -> bool
val redondance : unit -> int
val astuce : unit -> bool
val select : unit -> int
val cin : in_channel
val no_rm_eq_existential : unit -> bool
val nocontracongru : unit -> bool
val arrays : unit -> bool
val pairs : unit -> bool
val term_like_pp : unit -> bool
val debug_types : unit -> bool
val all_models : unit -> bool
val model : unit -> bool
val complete_model : unit -> bool
val smt_arrays : unit -> bool
val goal_directed : unit -> bool
val bouclage : unit -> int
val max_split : unit -> Num.num
val rewriting : unit -> bool
val proof : unit -> bool
val debug_proof : unit -> bool
val rules : unit -> int
val debug_split : unit -> bool
val restricted : unit -> bool
val bottom_classes : unit -> bool
val timelimit : unit -> float

val thread_yield : (unit -> unit) ref

val profiling : bool ref
val timer_start : (Timers.kind -> unit) ref
val timer_pause : (Timers.kind -> unit) ref
val timeout : (unit -> unit) ref

val replay : bool

val set_parse_only : bool -> unit
val set_type_only : bool -> unit
val set_stopb : int -> unit
val set_stepsb : int -> unit
val set_age_limite : int -> unit
val set_notriggers : bool -> unit
val set_debug : bool -> unit
val set_debug_cc : bool -> unit
val set_debug_use : bool -> unit
val set_debug_uf : bool -> unit
val set_debug_fm : bool -> unit
val set_debug_sum : bool -> unit
val set_debug_arith : bool -> unit
val set_debug_bitv : bool -> unit
val set_debug_ac : bool -> unit
val set_debug_sat : bool -> unit
val set_debug_sat_simple : bool -> unit
val set_debug_typing : bool -> unit
val set_debug_constr : bool -> unit
val set_debug_pairs : bool -> unit
val set_debug_arrays : bool -> unit
val set_debug_combine : bool -> unit
val set_verbose : bool -> unit
val set_debug_dispatch : bool -> unit
val set_tracefile : string -> unit
val set_bjmode : bool -> unit
val set_glouton : bool -> unit
val set_triggers_var : bool -> unit
val set_redondance : int -> unit
val set_astuce : bool -> unit
val set_select : int -> unit
val set_no_rm_eq_existential : bool -> unit
val set_nocontracongru : bool -> unit
val set_arrays : bool -> unit
val set_pairs : bool -> unit
val set_term_like_pp : bool -> unit
val set_debug_types : bool -> unit
val set_all_models : bool -> unit
val set_model : bool -> unit
val set_complete_model : bool -> unit
val set_smt_arrays : bool -> unit
val set_goal_directed : bool -> unit
val set_bouclage : int -> unit
val set_max_split : Num.num -> unit
val set_rewriting : bool -> unit
val set_proof : bool -> unit
val set_debug_proof : bool -> unit
val set_rules : int -> unit
val set_debug_split : bool -> unit
val set_restricted : bool -> unit
val set_bottom_classes : bool -> unit
val set_timelimit : float -> unit

val debug_custom : unit -> bool
val set_debug_custom : bool -> unit
val dmatching : bool
