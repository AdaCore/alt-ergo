(******************************************************************************)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2014 --- OCamlPro                                   *)
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

type view = private {f: Symbols.t ; xs: t list; ty: Ty.t; depth: int; tag: int;}

module Subst : sig
  include Map.S with type key = Symbols.t and type 'a t = 'a Symbols.Map.t
  val print :
    (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
end

type subst = t Subst.t * Ty.subst

module Map : Map.S with type key = t
module Set : Set.S with type elt = t

val view : t -> view
val make : Symbols.t -> t list -> Ty.t -> t

val shorten : t -> t

val vrai : t
val faux : t
val void : t

val int : string -> t
val real : string -> t
val bitv : string -> Ty.t -> t

val fresh_name : Ty.t -> t
val is_fresh : t -> bool
val is_int : t -> bool
val is_real : t -> bool

val compare : t -> t -> int
val equal : t -> t -> bool
val hash : t -> int

val vars_of : t -> Symbols.Set.t
val vars_of_as_term : t -> Set.t
val vty_of : t -> Ty.Svty.t

val pred : t -> t

val apply_subst : subst -> t -> t
val compare_subst : subst -> subst -> int
val fold_subst_term : (Symbols.t -> t -> 'b -> 'b) -> subst -> 'b -> 'b

val union_subst : subst -> subst -> subst

val add_label : Hstring.t -> t -> unit
val label : t -> Hstring.t
val is_in_model : t -> bool

val print : Format.formatter -> t -> unit
val print_list : Format.formatter -> t list -> unit
val print_list_sep : string -> Format.formatter -> t list -> unit
val print_tagged_classes : Format.formatter -> Set.t list -> unit

val dummy : t 

val subterms : Set.t -> t -> Set.t
val type_info : t -> Ty.t
val top : unit -> t
val bot : unit -> t
