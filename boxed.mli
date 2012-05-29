type t = { formula : Formula.t; (* Formula *)
           subst : Term.subst;  (* Substitution to be applied 
                                   (with known terms) *)
           polarity : bool;     (* Polarity of the formula *)
           view : Formula.t     (* apply_subst subst formula *)
         }

val print : Format.formatter -> t -> unit

val compare : t -> t -> int

val mk_not : t -> t

val apply_subst : Term.subst -> t -> t

val from_formula : Formula.t -> bool -> t

module Set : Set.S with type elt = t

module Map : Map.S with type key = t

val check_free_vars : t -> unit
