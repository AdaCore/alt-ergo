(******************************************************************************)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2015 --- OCamlPro                                   *)
(*     This file is distributed under the terms of the CeCILL-C licence       *)
(******************************************************************************)

(** [apply f [a_1; ...; a_n]] returns a couple [f a_1; ...; f a_n],
    same such that: (1) "same" is true if and only if a_i == a_i for
    each i; and (2) if same is true, then the resulting list is
    physically equal to the argument **)
val apply : ('a -> 'a) -> 'a list -> 'a list * bool

(** similar to function apply, but the elements of the list are
    couples **)
val apply_right : ('a -> 'a) -> ('b * 'a) list -> ('b * 'a) list * bool

(** An abbreviation of List.rev List.rev_map **)
val rrmap : ('a -> 'b) -> 'a list -> 'b list
