(******************************************************************************)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2015 --- OCamlPro                                   *)
(*     This file is distributed under the terms of the CeCILL-C licence       *)
(******************************************************************************)

module type S = sig
  type t

  val init : unit -> unit
  val decision : int -> unit
  val assume : int -> unit
  val query : unit -> unit
  val instantiation : int -> unit
  val instances : 'a list -> unit
  val bool_conflict : unit -> unit
  val theory_conflict : unit -> unit
  (* each boolean is true for Boolean conflict and false for Theory conflict *)
  val bcp_conflict : bool -> bool -> unit

  (* the boolean is true for Boolean red/elim and false for Theory red/elim *)
  val red : bool -> unit
  val elim : bool -> unit

  (* reset decision and matching levels *)
  val reset_dlevel : int -> unit
  val reset_ilevel : int -> unit

  (* record the when axioms are instantiated. Bool tells whether the instance
     is keeped or removed by the selector function *)
  val new_instance_of : string -> Loc.t -> bool -> unit
  val conflicting_instance : string -> Loc.t -> unit
  val register_produced_terms :
    string ->
    Loc.t ->
    Term.Set.t -> (* consumed *)
    Term.Set.t -> (* all terms of the instance *)
    Term.Set.t -> (* produced *)
    Term.Set.t -> (* produced that are new *)
    unit

  val print : bool -> int64 -> Timers.t -> Format.formatter -> unit
  val switch : unit -> unit
end

val get_current : unit -> (module S)
(** returns the current activated profiler. The default value is an
    internal module Profiling_default.M When the selected profiler is
    an external plugin, the first call of this function will attemp to
    dynamically load it **)

val set_current : (module S) -> unit
(** sets a new profiler. This function is intended to be used by dynamically
    loaded plugins **)
