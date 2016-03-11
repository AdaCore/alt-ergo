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

type binders = (Ty.t * int) Symbols.Map.t (*int tag in globally unique *)

type quantified = {
  name : string;
  main : t;
  triggers : (Term.t list * Literal.LT.t option) list;
  binders : binders;   (* quantified variable *)

  (* These fields should be (ordered) lists ! important for skolemization *)
  free_v : Term.t list; (* free variables in main *)
  free_vty : Ty.t list; (* free type variables in main *)
  loc : Loc.t; (* location of the "GLOBAL" axiom containing this quantified
                  formula. It forms with name a unique id *)
}

and llet = {
  let_var: Symbols.t;
  let_subst : Term.subst;
  let_term : Term.t;
  let_f : t;
}

and view =
    Unit of t*t  (* unit clauses *)
  | Clause of t*t      (* a clause (t1 or t2) *)
  | Literal of Literal.LT.t   (* an atom *)
  | Lemma of quantified   (* a lemma *)
  | Skolem of quantified  (* lazy skolemization *)
  | Let of llet (* a binding of a term *)


type gformula = {
  f: t;
  age: int;
  lem: t option;
  from_terms : Term.t list;
  mf: bool;
  gf: bool;
}

val mk_binders : Term.Set.t -> binders

val mk_not : t -> t
val mk_and : t -> t -> int -> t
val mk_or : t -> t -> int -> t
val mk_imp : t -> t -> int -> t
val mk_if : Term.t -> t -> t -> int -> t
val mk_iff : t -> t -> int -> t
val mk_lit : Literal.LT.t -> int -> t
val mk_forall :
  string -> (* name *)
  Loc.t -> (* location in the original file *)
  binders -> (* quantified variables *)
  (Term.t list * Literal.LT.t option) list -> (* triggers *)
  t -> (* quantified formula *)
  int -> (* id, for the GUI *)
  (Term.t list * Ty.t list) option ->
  (* free_vars and free_vty: they are computed if None is given *)
  t

val mk_exists :
  string -> (* name *)
  Loc.t -> (* location in the original file *)
  binders -> (* quantified variables *)
  (Term.t list * Literal.LT.t option) list -> (* triggers *)
  t -> (* quantified formula *)
  int -> (* id, for the GUI *)
  (Term.t list * Ty.t list) option ->
  (* free_vars and free_vty: they are computed if None is given *)
  t

val mk_let : Term.Set.t -> Symbols.t -> Term.t -> t -> int -> t

val add_label : Hstring.t -> t -> unit
val label : t -> Hstring.t
val is_in_model : t -> bool

val view : t -> view
val size : t -> int
val id : t -> int

val print : Format.formatter -> t -> unit

val ground_terms_rec : t -> Term.Set.t
val free_vars : t -> Term.Set.t Symbols.Map.t

val apply_subst : Term.subst -> t -> t

val compare : t -> t -> int
val equal : t -> t -> bool
val hash : t -> int
val vrai : t
val faux : t

val skolemize : quantified -> t

module Set : Set.S with type elt = t
module Map : Map.S with type key = t
