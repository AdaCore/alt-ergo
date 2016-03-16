(******************************************************************************)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2015 --- OCamlPro                                   *)
(*     This file is distributed under the terms of the CeCILL-C licence       *)
(******************************************************************************)

(******************************************************************************)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*   This file is distributed under the terms of the CeCILL-C licence         *)
(******************************************************************************)

type t

type exp =
  | Literal of Literal.LT.t
  | Fresh of int
  | Bj of Formula.t
  | Dep of Formula.t

val empty : t

val is_empty : t -> bool

val mem : exp -> t -> bool

val singleton : exp -> t

val union : t -> t -> t

val merge : t -> t -> t

val iter_atoms : (exp -> unit)  -> t -> unit

val fold_atoms : (exp -> 'a -> 'a )  -> t -> 'a -> 'a

val fresh_exp : unit -> exp

val remove_fresh : exp -> t -> t option

val remove : exp -> t -> t

val add_fresh : exp -> t -> t

val print : Format.formatter -> t -> unit

val print_proof : Format.formatter -> t -> unit

val formulas_of : t -> Formula.Set.t

val bj_formulas_of : t -> Formula.Set.t

module MI : Map.S with type key = int

val literals_ids_of : t -> int MI.t

val make_deps : Formula.Set.t -> t

val has_no_bj : t -> bool
