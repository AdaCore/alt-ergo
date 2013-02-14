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

open Why_ptree

val print_term : Format.formatter -> ('a tterm, 'a) annoted -> unit
val print_term_list : Format.formatter -> ('a tterm, 'a) annoted list -> unit

val print_form : Format.formatter -> ('a tform, 'a) annoted -> unit

(* print all structure inside formula *)

val print_tform : Format.formatter -> ('a tform, 'a) annoted -> unit

val print_typed_decl_list  :
    Format.formatter -> ?same_order:bool 
      -> (int tdecl, int) Why_ptree.annoted list -> unit

val print_typed_decl :
    Format.formatter -> (int tdecl, int) Why_ptree.annoted -> unit
