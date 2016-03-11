(******************************************************************************)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2015 --- OCamlPro                                   *)
(*     This file is distributed under the terms of the CeCILL-C licence       *)
(******************************************************************************)

(** cur_time, provided by Unix or by Javascript depending on the
    compilation mode: for byte/opt or for javascript **)

val cur_time : unit -> float

val set_timeout : float -> unit
val unset_timeout : unit -> unit
