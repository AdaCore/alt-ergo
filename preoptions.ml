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

(*let fmt = Format.std_formatter*)
let fmt = Format.err_formatter
let _ = 
  Format.pp_set_tags fmt true;
  Print_color.add_to_format_tag fmt

let file = ref " stdin"
let session_file = ref ""
let cin = ref stdin

let bouclage = ref 1
let smt_arrays = ref false
let rewriting = ref false
let type_only = ref false
let parse_only = ref false
let stopb = ref 8
let stepsb = ref (-1)
let age_limite = ref 10
let debug = ref false
let notriggers = ref false
let debug_cc = ref false
let debug_use = ref false
let debug_arrays = ref false
let debug_uf = ref false
let debug_sat = ref false
let debug_sat_simple = ref false
let debug_typing = ref false
let debug_constr = ref false
let debug_pairs = ref false
let verbose = ref false
let debug_fm = ref false
let debug_sum = ref false
let debug_arith = ref false
let debug_combine = ref false
let debug_bitv = ref false
let debug_ac = ref false
let debug_dispatch = ref false
let debug_split = ref false
let options = ref false
let tracefile = ref ""
let smtfile = ref false
let smt2file = ref false
let satmode = ref false
let bjmode = ref false
let glouton = ref false
let triggers_var = ref false
let redondance = ref 2
let astuce = ref false
let select = ref 0
let no_rm_eq_existential = ref false
let nocontracongru = ref false
let arrays = ref false
let pairs = ref false
let term_like_pp = ref true
let debug_types = ref false 
let all_models = ref false
let model = ref false
let complete_model = ref false
let goal_directed = ref false
let proof = ref false
let debug_proof = ref false
let rules = ref (-1)
let max_split = ref (Num.Int 1000000)
let restricted = ref false
let bottom_classes = ref false
let timelimit = ref 0.

let show_version () = Format.printf "%s@." Version.version; exit 0
let show_libdir () = Format.printf "%s@." Version.libdir; exit 0

let set_max_split s = 
  max_split := 
    try Num.num_of_string s 
    with Failure _ -> Num.Int (-1)

let set_proof b = proof := b

let set_rules = function
  | "parsing" -> rules := 0
  | "typing" -> rules := 1
  | "sat" -> rules := 2
  | "cc" -> rules := 3
  | "arith" -> rules := 4
  | _ -> rules := -1

let set_limit t =
  match Sys.os_type with
    | "Win32" -> Format.eprintf "timelimit not supported on Win32 (ignored)@."
    | _ -> timelimit := t

let replay = ref false

let debug_custom = ref false
