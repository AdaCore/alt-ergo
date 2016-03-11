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

module M : S = struct

  let failure () =
    Format.eprintf "@.%s %s@.@."
      "Error: This module is not implemented! You may want to complile"
      "and load the plugin provided in non-free/profiler/ instead";
    exit 1

  type t = unit
  let init _ = ()
  let query _ = failure ()
  let assume _ = failure ()
  let reset_dlevel _ = failure ()
  let reset_ilevel _ = failure ()
  let bcp_conflict _ = failure ()
  let theory_conflict _ = failure ()
  let bool_conflict _ = failure ()
  let red _ = failure ()
  let elim _ = failure ()
  let instantiation _ = failure ()
  let instances _ = failure ()
  let decision _ = failure ()
  let switch _ = failure ()
  let new_instance_of _ _ = failure ()
  let conflicting_instance _ _ = failure ()
  let register_produced_terms _ = failure ()
  let print_timers _ = failure ()
  let print _ = failure ()
end

let current = ref (module M : S)

let initialized = ref false

let set_current mdl = current := mdl

let load_current_module () =
  match Options.profiling_plugin () with
  | "" ->
    if Options.profiling() then
      Format.eprintf "[Dynlink] Using the default profiler@."

  | path ->
    if Options.profiling() then
      Format.eprintf "[Dynlink] Loading the profiler in %s ...@." path;
    try
      Dynlink.loadfile path;
      if Options.profiling() then Format.eprintf "Success !@.@."
    with
    | Dynlink.Error m1 ->
      if Options.profiling() then begin
        Format.eprintf
          "[Dynlink] Loading the profiler in plugin \"%s\" failed!@."
          path;
        Format.eprintf ">> Failure message: %s@.@." (Dynlink.error_message m1);
      end;
      let prefixed_path = Format.sprintf "%s/%s" Config.pluginsdir path in
      if Options.profiling() then
        Format.eprintf
          "[Dynlink] Loading the profiler in %s ... with prefix %s@."
          path Config.pluginsdir;
      try
        Dynlink.loadfile prefixed_path;
        if Options.profiling() then Format.eprintf "Success !@.@."
      with
      | Dynlink.Error m2 ->
        if not (Options.profiling()) then begin
          Format.eprintf
            "[Dynlink] Loading the profiler in plugin \"%s\" failed!@."
            path;
          Format.eprintf ">> Failure message: %s@.@."
            (Dynlink.error_message m1);
        end;
        Format.eprintf
          "[Dynlink] Trying to load the plugin from \"%s\" failed too!@."
          prefixed_path;
        Format.eprintf ">> Failure message: %s@.@." (Dynlink.error_message m2);
        exit 1

let get_current () =
  if Options.profiling () && not !initialized then
    begin
      load_current_module ();
      initialized := true;
    end;
  !current
