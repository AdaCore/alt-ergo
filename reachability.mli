open Sig

module Make 
  (X : Sig.X) :
sig
  type t

  val empty : unit -> t
  
  val assume : 
    t ->
    (X.r input) list -> 
    are_eq : (Term.t -> Term.t -> answer) -> 
    are_neq : (Term.t -> Term.t -> answer) -> 
    class_of : (Term.t -> Term.t list) ->
    find : (Term.t -> X.r * Explanation.t) ->
    t * X.r result

  val case_split : t -> (X.r Literal.view * Explanation.t * Num.num) list

end
