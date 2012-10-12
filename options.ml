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

open Preoptions

let fmt = fmt
let file = file
let session_file = session_file
let satmode = satmode
let smt2file = smt2file
let smtfile = smtfile

let cin = !cin

let type_only () = !type_only
let parse_only () = !parse_only
let stopb () = !stopb
let stepsb () = !stepsb
let age_limite () = !age_limite
let notriggers () = !notriggers
let debug () = !debug
let debug_cc () = !debug_cc
let debug_use () = !debug_use
let debug_uf () = !debug_uf
let debug_fm () = !debug_fm
let debug_sum () = !debug_sum
let debug_arith () = !debug_arith
let debug_bitv () = !debug_bitv
let debug_ac   () = !debug_ac
let debug_sat () = !debug_sat
let debug_sat_simple () = !debug_sat_simple
let debug_typing () = !debug_typing
let debug_constr () = !debug_constr
let debug_pairs () = !debug_pairs
let verbose () = !verbose
let debug_dispatch () = !debug_dispatch
let tracefile () = !tracefile
let bjmode () = !bjmode
let glouton () = !glouton
let triggers_var () = !triggers_var
let redondance () = !redondance
let astuce () = !astuce
let select () = !select
let no_rm_eq_existential () = !no_rm_eq_existential
let nocontracongru () = !nocontracongru
let arrays () = !arrays
let pairs () = !pairs
let term_like_pp () = !term_like_pp
let debug_arrays () = !debug_arrays
let debug_types () = !debug_types
let all_models () = !all_models
let model () = !model || !complete_model
let complete_model () = !complete_model
let debug_combine () = !debug_combine
let smt_arrays () = ! smt_arrays
let goal_directed () = !goal_directed
let bouclage () = ! bouclage
let max_split () = !max_split
let rewriting () = !rewriting
let proof () = !proof
let debug_proof () = !debug_proof && proof ()
let rules () = !rules
let debug_split () = !debug_split
let restricted () = !restricted
let bottom_classes () = !bottom_classes
let timelimit () = !timelimit

let thread_yield = ref (fun () -> ())

let profiling = ref false
let timer_start = ref (fun _ -> ())
let timer_pause = ref (fun _ -> ())
let timeout = ref (fun () -> Format.printf "Timeout@."; exit 142)

let replay = !replay


let set_type_only b = Preoptions.type_only := b
let set_parse_only b = Preoptions.parse_only := b
let set_stopb b = Preoptions.stopb := b
let set_stepsb b = Preoptions.stepsb := b
let set_age_limite b = Preoptions.age_limite := b
let set_notriggers b = Preoptions.notriggers := b
let set_debug b = Preoptions.debug := b
let set_debug_cc b = Preoptions.debug_cc := b
let set_debug_use b = Preoptions.debug_use := b
let set_debug_uf b = Preoptions.debug_uf := b
let set_debug_fm b = Preoptions.debug_fm := b
let set_debug_sum b = Preoptions.debug_sum := b
let set_debug_arith b = Preoptions.debug_arith := b
let set_debug_bitv b = Preoptions.debug_bitv := b
let set_debug_ac   b = Preoptions.debug_ac := b
let set_debug_sat b = Preoptions.debug_sat := b
let set_debug_sat_simple b = Preoptions.debug_sat_simple := b
let set_debug_typing b = Preoptions.debug_typing := b
let set_debug_constr b = Preoptions.debug_constr := b
let set_debug_pairs b = Preoptions.debug_pairs := b
let set_verbose b = Preoptions.verbose := b
let set_debug_dispatch b = Preoptions.debug_dispatch := b
let set_tracefile b = Preoptions.tracefile := b
let set_bjmode b = Preoptions.bjmode := b
let set_glouton b = Preoptions.glouton := b
let set_triggers_var b = Preoptions.triggers_var := b
let set_redondance b = Preoptions.redondance := b
let set_astuce b = Preoptions.astuce := b
let set_select b = Preoptions.select := b
let set_no_rm_eq_existential b = Preoptions.no_rm_eq_existential := b
let set_nocontracongru b = Preoptions.nocontracongru := b
let set_arrays b = Preoptions.arrays := b
let set_pairs b = Preoptions.pairs := b
let set_term_like_pp b = Preoptions.term_like_pp := b
let set_debug_arrays b = Preoptions.debug_arrays := b
let set_debug_types b = Preoptions.debug_types := b
let set_all_models b = Preoptions.all_models := b
let set_model b = Preoptions.model := b
let set_complete_model b = Preoptions.complete_model := b
let set_debug_combine b = Preoptions.debug_combine := b
let set_smt_arrays b = Preoptions. smt_arrays := b
let set_goal_directed b = Preoptions.goal_directed := b
let set_bouclage b = Preoptions.bouclage := b
let set_max_split b = Preoptions.max_split := b
let set_rewriting b = Preoptions.rewriting := b
let set_proof b = Preoptions.proof := b
let set_debug_proof b = Preoptions.debug_proof := b
let set_rules b = Preoptions.rules := b
let set_debug_split b = Preoptions.debug_split := b
let set_restricted b = Preoptions.restricted := b
let set_bottom_classes b = Preoptions.bottom_classes := b
let set_timelimit b = Preoptions.timelimit := b

let debug_custom () = !debug_custom
let set_debug_custom b = Preoptions.debug_custom := b
let dmatching = !debug_matching
