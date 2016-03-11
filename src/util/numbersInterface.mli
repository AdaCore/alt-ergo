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

(** Interface of Integers **)
module type ZSig = sig
  type t
  val zero : t
  val one : t
  val m_one : t (* minus one *)

  val compare : t -> t -> int
  val compare_to_0 : t -> int
  val equal   : t -> t -> bool
  val sign : t -> int
  val hash : t -> int

  val is_zero : t -> bool
  val is_one : t -> bool
  val is_m_one : t -> bool

  val add : t -> t -> t
  val sub : t -> t -> t
  val mult : t -> t -> t
  val div : t -> t -> t
  val rem : t -> t -> t
  val div_rem : t -> t -> t * t
  val minus : t -> t
  val abs  : t -> t
  val my_gcd : t -> t -> t
  val my_lcm : t -> t -> t
  val max : t -> t -> t
  val from_int : int -> t
  val from_string : string -> t
  val to_string : t -> string

  val to_float : t -> float
  val fdiv : t -> t -> t
  val cdiv : t -> t -> t
  val power : t -> int -> t

  val print : Format.formatter -> t -> unit
end


(** Interface of Rationals **)
module type QSig = sig

  module Z : ZSig

  type t

  exception Not_a_float

  val num : t -> Z.t
  val den : t -> Z.t

  val zero : t
  val one : t
  val m_one : t (* minus one *)

  val compare : t -> t -> int
  val compare_to_0 : t -> int
  val equal   : t -> t -> bool
  val sign : t -> int
  val hash : t -> int

  val is_zero : t -> bool
  val is_one : t -> bool
  val is_m_one : t -> bool
  val is_int : t -> bool

  val add : t -> t -> t
  val sub : t -> t -> t
  val mult : t -> t -> t
  val div : t -> t -> t
  val minus : t -> t
  val abs : t -> t
  val min : t -> t -> t
  val inv : t -> t
  (* Euclidean division's remainder. Assumes that the arguments are in Z *)
  val modulo : t -> t -> t

  val from_float : float -> t
  val from_int : int -> t
  val from_z : Z.t -> t
  val from_zz: Z.t -> Z.t -> t
  val from_string : string -> t
  val to_float : t -> float
  val to_z : t -> Z.t (* Assumes that the argument is in Z *)
  val to_string : t -> string

  val print : Format.formatter -> t -> unit

  val power : t -> int -> t
  val floor : t -> t
  val ceiling : t -> t

end
