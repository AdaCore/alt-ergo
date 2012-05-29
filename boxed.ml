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
(*     Claire Dross                                                       *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

type t = { formula : Formula.t;
           subst : Term.subst;
           polarity : bool;
           view : Formula.t
         } 

let compare b1 b2 =
  let c = compare b1.polarity b2.polarity in 
  if c<>0 then c else Formula.compare b1.view b2.view

module Boxed = struct 
  type tmp = t
  type t = tmp
  let compare = compare
end

module Set = Set.Make (Boxed)

module Map = Map.Make (Boxed)

let mk_not b = { formula = Formula.mk_not b.formula;
                 subst = b.subst;
                 polarity = not b.polarity;
                 view = Formula.mk_not b.view }

let print fmt b = 
  if b.polarity then Format.fprintf fmt "(+) %a" Formula.print b.view
  else Format.fprintf fmt "(-) %a" Formula.print b.view

let apply_subst s b = { b with subst = Term.union_subst s b.subst;
  view = Formula.apply_subst s b.view }

let from_formula f pol = { formula = f; view = f; 
                           polarity = pol; 
                           subst = Symbols.Map.empty, Ty.esubst }

let check_free_vars b =
  let vars = Formula.free_vars b.view in
  if not (Symbols.Set.is_empty vars) then
    (Format.fprintf Options.fmt "---- %a@." 
       (fun fmt v -> Symbols.Set.iter (Symbols.print fmt) v) vars;
     failwith "free vars after subst !");
