(******************************************************************************)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2015 --- OCamlPro                                   *)
(*     This file is distributed under the terms of the CeCILL-C licence       *)
(******************************************************************************)

module MI : Map.S with type key = int

(*
(** This function is intended to be used with Map.merge in order to perform a
    union of two maps. The first argument is an equality function used to
    assert that bindings present in boths maps have the same value **)
val map_merge_is_union :
  ('a -> 'a -> bool) -> 'b ->
  ('a * int) option -> ('a * int) option -> ('a * int) option
*)
