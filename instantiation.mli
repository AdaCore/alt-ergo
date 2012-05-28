module Make (Uf : Uf.S) (Use : Use.S with type r = Uf.R.r)
  (CC : Sig.CC with type Rel.r = Use.r
  with type 'a accumulator = 
         ('a Sig.literal * Explanation.t) list * ('a * 'a * Explanation.t) list 
  with type use = Use.t
  with type uf = Uf.t) : sig

  type t

  val empty : t

  type update = Use.r * Use.r * Explanation.t

  type witness = Term.t list * Term.subst * Explanation.t

  type trigger = Term.t list * Term.subst * Explanation.t * Boxed.t

  type quantifier = 
      Boxed.t * Symbols.Set.t * Boxed.t * Term.t list * Term.subst
      * Explanation.t

  type env = (Use.r Sig.literal * Explanation.t) list * t * CC.env

  val is_known : env -> (Term.t * Term.subst) -> Sig.answer

  val update : env -> update list -> env * (Boxed.t * Explanation.t) list

  val add_witness : env -> witness -> env * (Boxed.t * Explanation.t) list

  val add_trigger : env -> trigger -> env * (Boxed.t * Explanation.t) list

  val add_quantifier : env -> quantifier -> env * (Boxed.t * Explanation.t) list

end
