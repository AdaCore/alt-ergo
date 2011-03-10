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

type loc = Lexing.position * Lexing.position

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
  | PPextract of lexpr * lexpr * lexpr
  | PPconcat of lexpr * lexpr
  | PPif of lexpr * lexpr * lexpr
  | PPforall of string list * ppure_type * lexpr list list * lexpr
  | PPexists of string list * ppure_type * lexpr
  | PPnamed of string * lexpr
  | PPlet of string * lexpr * lexpr

(* Declarations. *)

type plogic_type =
  | PPredicate of ppure_type list
  | PFunction of ppure_type list * ppure_type

type name_kind = Symbols.name_kind

type decl = 
  | Axiom of loc * string * lexpr
  | Rewriting of loc * string * lexpr list
  | Goal of loc * string * lexpr
  | Logic of loc * name_kind * string list * plogic_type
  | Predicate_def of loc * string * (loc * string * ppure_type) list * lexpr
  | Function_def 
      of loc * string * (loc * string * ppure_type) list * ppure_type * lexpr
  | TypeDecl of loc * string list * string * string list

type file = decl list

(*** typed ast *)

type tconstant =
  | Tint of string
  | Treal of Num.num
  | Tbitv of string
  | Ttrue
  | Tfalse
  | Tvoid

type 'a tterm = 
    { tt_ty : Ty.t; tt_desc : 'a tt_desc; tt_annot : 'a }
and 'a tt_desc = 
  | TTconst of tconstant
  | TTvar of Symbols.t
  | TTinfix of 'a tterm * Symbols.t * 'a tterm
  | TTprefix of Symbols.t * 'a tterm 
  | TTapp of Symbols.t * 'a tterm list
  | TTget of 'a tterm * 'a tterm
  | TTset of 'a tterm * 'a tterm * 'a tterm
  | TTextract of 'a tterm * 'a tterm * 'a tterm
  | TTconcat of 'a tterm * 'a tterm
  | TTlet of Symbols.t * 'a tterm * 'a tterm

type 'a tatom = 
  | TAtrue
  | TAfalse
  | TAeq of 'a * 'a tterm list
  | TAdistinct of 'a * 'a tterm list
  | TAneq of 'a * 'a tterm list
  | TAle of 'a * 'a tterm list
  | TAlt of 'a * 'a tterm list
  | TApred of 'a * 'a tterm
  | TAbuilt of 'a * Hstring.t * 'a tterm list

type 'a oplogic = OPand |OPor | OPimp | OPnot | OPif of 'a tterm | OPiff 

type 'a quant_form = {       
  (* quantified variables that appear in the formula *)
  qf_bvars : (Symbols.t * Ty.t) list ;

  qf_upvars : (Symbols.t * Ty.t) list ;

  qf_triggers : 'a tterm list list ;
  qf_form : 'a tform
}

and 'a tform =
  | TFatom of 'a * 'a tatom
  | TFop of 'a * 'a oplogic * 'a tform list
  | TFforall of 'a * 'a quant_form
  | TFexists of 'a * 'a quant_form
  | TFlet of 'a * (Symbols.t * Ty.t) list * Symbols.t * 'a tterm * 'a tform
  | TFnamed of 'a * Hstring.t * 'a tform


type 'a rwt_rule = {
  rwt_vars : (Symbols.t * Ty.t) list;
  rwt_left : 'a;
  rwt_right : 'a
}

type 'a tdecl = 
  | TAxiom of 'a * loc * string * 'a tform
  | TRewriting of 'a * loc * string * ('a tterm rwt_rule) list
  | TGoal of 'a * loc * string * 'a tform
  | TLogic of 'a * loc * string list * plogic_type
  | TPredicate_def of 'a * loc * string * (string * ppure_type) list * 'a tform
  | TFunction_def 
      of 'a * loc * string * (string * ppure_type) list * ppure_type * 'a tform
  | TTypeDecl of 'a * loc * string list * string * string list


(* Sat entry *)

type sat_decl_aux = 
  | Assume of Formula.t * bool 
  | PredDef of Formula.t
  | RwtDef of (Term.t rwt_rule) list
  | Query of string * Formula.t * Literal.LT.t list

type sat_tdecl = {
  st_loc : loc;
  st_decl : sat_decl_aux
}
