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

open Loc
open Format

type constant =
  | ConstBitv of string
  | ConstInt of string
  | ConstReal of Num.num
  | ConstTrue
  | ConstFalse
  | ConstVoid

type pp_infix = 
  | PPand | PPor | PPimplies | PPiff 
  | PPlt | PPle | PPgt | PPge | PPeq | PPneq
  | PPadd | PPsub | PPmul | PPdiv | PPmod
      
type pp_prefix = 
  | PPneg | PPnot

type ppure_type =
  | PPTint
  | PPTbool
  | PPTreal
  | PPTunit
  | PPTbitv of int
  | PPTvarid of string * loc
  | PPTexternal of ppure_type list * string * loc
      
type lexpr = 
    { pp_loc : loc; pp_desc : pp_desc }

and pp_desc =
  | PPvar of string
  | PPapp of string * lexpr list
  | PPdistinct of lexpr list
  | PPconst of constant
  | PPinfix of lexpr * pp_infix * lexpr
  | PPprefix of pp_prefix * lexpr
  | PPget of lexpr * lexpr
  | PPset of lexpr * lexpr * lexpr
  | PPdot of lexpr * string
  | PPrecord of (string * lexpr) list
  | PPwith of lexpr * (string * lexpr) list
  | PPextract of lexpr * lexpr * lexpr
  | PPconcat of lexpr * lexpr
  | PPif of lexpr * lexpr * lexpr
  | PPforall of string list * ppure_type * lexpr list list * lexpr
  | PPexists of string list * ppure_type * lexpr list list * lexpr
  | PPforall_named of 
      (string * string) list * ppure_type * lexpr list list * lexpr
  | PPexists_named of
      (string * string) list * ppure_type * lexpr list list * lexpr
  | PPnamed of string * lexpr
  | PPlet of string * lexpr * lexpr
  | PPcheck of lexpr
  | PPcut of lexpr
  | PPcast of lexpr * ppure_type

(* Declarations. *)

type plogic_type =
  | PPredicate of ppure_type list
  | PFunction of ppure_type list * ppure_type

type name_kind = Symbols.name_kind

type body_type_decl = 
  | Record of (string * ppure_type) list  (* lbl : t *)
  | Enum of string list
  | Abstract

type decl = 
  | Axiom of loc * string * lexpr
  | Rewriting of loc * string * lexpr list
  | Goal of loc * string * lexpr
  | Logic of loc * name_kind * (string * string) list * plogic_type
  | Predicate_def of 
      loc * (string * string) * 
	(loc * string * ppure_type) list * lexpr
  | Function_def of 
      loc * (string * string) * 
	(loc * string * ppure_type) list * ppure_type * lexpr
  | TypeDecl of loc * string list * string * body_type_decl

type file = decl list

(*** typed ast *)

type ('a, 'b) annoted =
    { c : 'a;
      annot : 'b }

type tconstant =
  | Tint of string
  | Treal of Num.num
  | Tbitv of string
  | Ttrue
  | Tfalse
  | Tvoid

type 'a tterm = 
    { tt_ty : Ty.t; tt_desc : 'a tt_desc }
and 'a tt_desc = 
  | TTconst of tconstant
  | TTvar of Symbols.t
  | TTinfix of ('a tterm, 'a) annoted * Symbols.t * ('a tterm, 'a) annoted
  | TTprefix of Symbols.t * ('a tterm, 'a) annoted 
  | TTapp of Symbols.t * ('a tterm, 'a) annoted list
  | TTget of ('a tterm, 'a) annoted * ('a tterm, 'a) annoted
  | TTset of 
      ('a tterm, 'a) annoted * ('a tterm, 'a) annoted * ('a tterm, 'a) annoted
  | TTextract of 
      ('a tterm, 'a) annoted * ('a tterm, 'a) annoted * ('a tterm, 'a) annoted
  | TTconcat of ('a tterm, 'a) annoted * ('a tterm, 'a) annoted
  | TTdot of ('a tterm, 'a) annoted * Hstring.t
  | TTrecord of (Hstring.t * ('a tterm, 'a) annoted) list
  | TTlet of Symbols.t * ('a tterm, 'a) annoted * ('a tterm, 'a) annoted
  | TTnamed of Hstring.t * ('a tterm, 'a) annoted

type 'a tatom = 
  | TAtrue
  | TAfalse
  | TAeq of ('a tterm, 'a) annoted list
  | TAdistinct of ('a tterm, 'a) annoted list
  | TAneq of ('a tterm, 'a) annoted list
  | TAle of ('a tterm, 'a) annoted list
  | TAlt of ('a tterm, 'a) annoted list
  | TApred of ('a tterm, 'a) annoted
  | TAbuilt of Hstring.t * ('a tterm, 'a) annoted list

type 'a oplogic = 
    OPand |OPor | OPimp | OPnot | OPiff 
  | OPif of ('a tterm, 'a) annoted

type 'a quant_form = {       
  (* quantified variables that appear in the formula *)
  qf_bvars : (Symbols.t * Ty.t) list ;
  qf_upvars : (Symbols.t * Ty.t) list ;
  qf_triggers : ('a tterm, 'a) annoted list list ;
  qf_form : ('a tform, 'a) annoted
}

and 'a tform =
  | TFatom of ('a tatom, 'a) annoted
  | TFop of 'a oplogic * (('a tform, 'a) annoted) list
  | TFforall of 'a quant_form
  | TFexists of 'a quant_form
  | TFlet of (Symbols.t * Ty.t) list * Symbols.t * 
      ('a tterm, 'a) annoted * ('a tform, 'a) annoted
  | TFnamed of Hstring.t * ('a tform, 'a) annoted


type 'a rwt_rule = {
  rwt_vars : (Symbols.t * Ty.t) list;
  rwt_left : 'a;
  rwt_right : 'a
}

type goal_sort = Cut | Check | Thm

type 'a tdecl = 
  | TAxiom of loc * string * ('a tform, 'a) annoted
  | TRewriting of loc * string * (('a tterm, 'a) annoted rwt_rule) list
  | TGoal of loc * goal_sort * string * ('a tform, 'a) annoted
  | TLogic of loc * string list * plogic_type
  | TPredicate_def of 
      loc * string *
	(string * ppure_type) list * ('a tform, 'a) annoted
  | TFunction_def of 
      loc * string *
	(string * ppure_type) list * ppure_type * ('a tform, 'a) annoted
  | TTypeDecl of loc * string list * string * body_type_decl


(* Sat entry *)

type sat_decl_aux = 
  | Assume of Formula.t * bool
  | PredDef of Formula.t
  | RwtDef of (Term.t rwt_rule) list
  | Query of string *  Formula.t * Literal.LT.t list * goal_sort

type sat_tdecl = {
  st_loc : loc;
  st_decl : sat_decl_aux
}

(*****)
let rec print_term fmt t = match t.c.tt_desc with
  | TTconst Ttrue -> 
    fprintf fmt "true"
  | TTconst Tfalse -> 
    fprintf fmt "false"
  | TTconst Tvoid -> 
    fprintf fmt "void"
  | TTconst (Tint n) -> 
    fprintf fmt "%s" n
  | TTconst (Treal n) -> 
    fprintf fmt "%s" (Num.string_of_num n)
  | TTconst Tbitv s -> 
    fprintf fmt "%s" s
  | TTvar s -> 
    fprintf fmt "%a" Symbols.print s
  | TTapp(s,l) -> 
    fprintf fmt "%a(%a)" Symbols.print s print_term_list l
  | TTinfix(t1,s,t2) -> 
    fprintf fmt "%a %a %a" print_term t1 Symbols.print s print_term t2
  | TTprefix (s, t') ->
    fprintf fmt "%a %a" Symbols.print s print_term t'
  | TTget (t1, t2) ->
    fprintf fmt "%a[%a]" print_term t1 print_term t2
  | TTset (t1, t2, t3) ->
    fprintf fmt "%a[%a<-%a]" print_term t1 print_term t2 print_term t3
  | TTextract (t1, t2, t3) ->
    fprintf fmt "%a^{%a,%a}" print_term t1 print_term t2 print_term t3
  | TTconcat (t1, t2) ->
    fprintf fmt "%a @ %a" print_term t1 print_term t2
  | TTdot (t1, s) ->
    fprintf fmt "%a.%s" print_term t1 (Hstring.view s)
  | TTrecord l ->
    fprintf fmt "{ ";
    List.iter 
      (fun (s, t) -> fprintf fmt "%s = %a" (Hstring.view s) print_term t) l;
    fprintf fmt " }"
  | TTlet (s, t1, t2) ->
    fprintf fmt "let %a=%a in %a" Symbols.print s print_term t1 print_term t2
  | TTnamed (lbl, t) ->
    fprintf fmt "%a" print_term t

and print_term_list fmt = List.iter (fprintf fmt "%a," print_term)

let print_atom fmt a = 
  match a.c with
    | TAtrue ->
      fprintf fmt "True"
    | TAfalse ->
      fprintf fmt "True"
    | TAeq [t1; t2] -> 
      fprintf fmt "%a = %a" print_term t1 print_term t2
    | TAneq [t1; t2] ->
      fprintf fmt "%a <> %a" print_term t1 print_term t2
    | TAle [t1; t2] ->
      fprintf fmt "%a <= %a" print_term t1 print_term t2
    | TAlt [t1; t2] ->
      fprintf fmt "%a < %a" print_term t1 print_term t2
    | TApred t -> 
      print_term fmt t
    | TAbuilt(s, l) ->
      fprintf fmt "%s(%a)" (Hstring.view s) print_term_list l
    | _ -> assert false

let string_of_op = function
  | OPand -> "and"
  | OPor -> "or"
  | OPimp -> "->"
  | OPiff -> "<->"
  | _ -> assert false

let print_binder fmt (s, t) =
  fprintf fmt "%a :%a" Symbols.print s Ty.print t

let print_binders fmt l = 
  List.iter (fun c -> fprintf fmt "%a, " print_binder c) l

let print_triggers fmt = List.iter (fprintf fmt "%a | " print_term_list)
  
let rec print_formula fmt f = 
  match f.c with
    | TFatom a -> 
      print_atom fmt a
    | TFop(OPnot, [f]) -> 
      fprintf fmt "not %a" print_formula f
    | TFop(OPif(t), [f1;f2]) -> 
      fprintf fmt "if %a then %a else %a" 
	print_term t print_formula f1 print_formula f2
    | TFop(op, [f1; f2]) -> 
      fprintf fmt "%a %s %a" print_formula f1 (string_of_op op) print_formula f2
    | TFforall {qf_bvars = l; qf_triggers = t; qf_form = f} -> 
      fprintf fmt "forall %a [%a]. %a" 
	print_binders l print_triggers t print_formula f
    | _ -> assert false

and print_form_list fmt = List.iter (fprintf fmt "%a" print_formula)
