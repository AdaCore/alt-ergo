(* Add the axiomatization *)
val add_theory : Formula.t list -> unit

module Make (Uf : Uf.S) (Use : Use.S with type r = Uf.R.r)
  (CC : Sig.CC with type Rel.r = Use.r
  with type 'a accumulator = 
                      ('a Sig.literal * Explanation.t) list * 
                        ('a * 'a * Explanation.t) list 
  with type use = Use.t
  with type uf = Uf.t): 
  Sig.CC with type Rel.r = Use.r
  with type 'a accumulator = ('a Sig.literal * Explanation.t) list 
  with type use = Use.t
  with type uf = Uf.t
