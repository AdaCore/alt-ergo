(**************************************************************************)
(*                                                                        *)
(*     The Alt-ergo theorem prover                                        *)
(*     Copyright (C) 2006-2010                                            *)
(*                                                                        *)
(*     Sylvain Conchon                                                    *)
(*     Evelyne Contejean                                                  *)
(*     Stephane Lescuyer                                                  *)
(*     Mohamed Iguernelala                                                *)
(*     Alain Mebsout                                                      *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

type answer = Yes of Explanation.t | No

type 'a ac = {h: Symbols.t ; t: Ty.t ; l: ('a * int) list}

type 'a sem_atom =  'a Literal.view * Literal.LT.t option

type 'a sem_atom_ex =  'a Literal.view * Literal.LT.t option * Explanation.t

module type RELATION = sig
  type t
  type r

  val empty : unit -> t
  
  val assume : 
    t -> r sem_atom_ex list -> Explanation.t -> t * r sem_atom_ex list

  val instantiate :
    t -> 
    (Term.t -> Term.t -> answer) -> 
    (Term.t -> Term.t -> answer) -> 
    (Term.t -> Term.t list)      ->
    r sem_atom list ->  
    t * Literal.LT.t list

  val query : r sem_atom -> t -> Explanation.t -> answer

  val case_split : t -> (r sem_atom * Num.num) list
    (** case_split env returns a list of equalities *)
    
  val add : t -> r -> t
    (** add a representant to take into account *)

end

module type THEORY = sig

  (**Type of terms of the theory*)
  type t
  (**Type of representants of terms of the theory*)
  type r
  (** Name of the theory*)
  val name : string
  (** return true if the atom is owned by the theory*)
  val is_mine_a : Literal.LT.t -> bool
  (** return true if the symbol is owned by the theory*)
  val is_mine_symb : Symbols.t -> bool
  (** return true if the type is owned by the theory*)
  val is_mine_type : t -> bool

  (** return true when the argument is an unsolvable function of the theory *)
  val unsolvable : t -> bool

  (** Give a representant of a term of the theory*)
  val make : Term.t -> r * Literal.LT.t list

  val color : (r ac) -> r
  
  val type_info : t -> Ty.t
    
  val embed : r -> t

  (** Give the leaves of a term of the theory *)
  val leaves : t -> r list
  val subst : r -> r -> t -> r

  val compare : t -> t -> int

  val hash : t -> int
  (** solve r1 r2, solve the equality r1=r2 and return the substitution *)

  val solve : r -> r ->  (r * r) list

  val print : Format.formatter -> t -> unit

  val fully_interpreted : Symbols.t -> bool

  module Rel : RELATION with type r = r
end

module type COMBINATOR = sig
  type r
  type th

  val extract : r -> th
  val make : Term.t -> r * Literal.LT.t list
  val type_info : r -> Ty.t
  val compare : r -> r -> int
  val leaves : r -> r list
  val subst : r -> r -> r -> r
  val solve : r -> r ->  (r * r) list
  val empty_embedding : Term.t -> r
  val normal_form : Literal.LT.t -> Literal.LT.t
  val print : Format.formatter -> r -> unit
  module Rel : RELATION with type r = r

end

module type X = sig
  type r

  val make : Term.t -> r * Literal.LT.t list
  
  val type_info : r -> Ty.t
  
  val compare : r -> r -> int
  
  val equal : r -> r -> bool

  val hash : r -> int
  
  val leaves : r -> r list
  
  val subst : r -> r -> r -> r
  
  val solve : r -> r ->  (r * r) list
  
  val term_embed : Term.t -> r

  val term_extract : r -> Term.t option 
  
  val ac_embed : r ac -> r
  
  val ac_extract : r -> (r ac) option
  
  val color : (r ac) -> r

  val unsolvable   : r -> bool

  val fully_interpreted : Symbols.t -> bool
  
  val print : Format.formatter -> r -> unit
  
  module Rel : RELATION with type r = r

end

module type C = sig
  type t
  type r
  val extract : r -> t option
  val embed : t -> r
end

module type EXPLANATION = sig
  type t = Formula.Set.t option

  val union : t -> t-> t
end
