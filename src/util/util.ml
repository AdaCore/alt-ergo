(******************************************************************************)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2015 --- OCamlPro                                   *)
(*     This file is distributed under the terms of the CeCILL-C licence       *)
(******************************************************************************)

exception Timeout

module MI = Map.Make(struct type t = int let compare a b = a - b end)

(** Different values for -case-split-policy option:
 -after-theory-assume (default value): after assuming facts in theory by the SAT
 -before-matching: just before performing a matching round
 -after-matching: just after performing a matching round
 **)
type case_split_policy =
  | AfterTheoryAssume (* default *)
  | BeforeMatching
  | AfterMatching

(*
let map_merge_is_union eq k a b =
  match a, b with
  | None, None     -> None
  | None, Some _   -> b
  | Some _, None   -> a
  | Some (x, c1), Some (y, c2) -> assert (eq x y); Some (x, c1 + c2)
*)
