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

type sbuffer = GSourceView2.source_buffer

type error_model = {
  mutable some : bool;
  rcols : GTree.column_list;
  rcol_icon : GtkStock.id GTree.column;
  rcol_desc : String.t GTree.column;
  rcol_line : int GTree.column;
  rcol_type : int GTree.column;
  rcol_color : String.t GTree.column;
  rstore : GTree.list_store;
}

type inst_model = {
  h : (int, Gtk.tree_iter option ref * int ref * string * int ref) Hashtbl.t;
  mutable max : int;
  icols : GTree.column_list;
  icol_icon : GtkStock.id GTree.column;
  icol_desc : String.t GTree.column;
  icol_number : int GTree.column;
  icol_limit : String.t GTree.column;
  icol_tag : int GTree.column;
  istore : GTree.list_store;
}

type 'a annoted =
    { mutable c : 'a; 
      mutable pruned : bool;
      mutable polarity : bool;
      tag : GText.tag;
      ptag : GText.tag;
      id : int;
      buf : sbuffer;
      mutable line : int;
 }

type aterm = 
    { at_ty : Ty.t; at_desc : at_desc }

and at_desc = 
  | ATconst of tconstant
  | ATvar of Symbols.t
  | ATapp of Symbols.t * aterm list
  | ATinfix of aterm * Symbols.t * aterm
  | ATprefix of Symbols.t * aterm 
  | ATget of aterm * aterm
  | ATset of aterm * aterm * aterm
  | ATextract of aterm * aterm * aterm
  | ATconcat of aterm * aterm
  | ATlet of Symbols.t * aterm * aterm
  | ATdot of aterm * Hstring.t
  | ATrecord of (Hstring.t * aterm) list
      

type aatom = 
  | AAtrue
  | AAfalse
  | AAeq of aterm annoted list
  | AAneq of aterm annoted list
  | AAdistinct of aterm annoted list
  | AAle of aterm annoted list
  | AAlt of aterm annoted list
  | AApred of aterm
  | AAbuilt of Hstring.t * aterm annoted list

type aoplogic =
    AOPand |AOPor | AOPimp | AOPnot | AOPif of aterm | AOPiff 

type aquant_form = {       
  aqf_bvars : (Symbols.t * Ty.t) list ;
  aqf_upvars : (Symbols.t * Ty.t) list ;
  mutable aqf_triggers : aterm annoted list list ;
  aqf_form : aform annoted
}

and aform =
  | AFatom of aatom
  | AFop of aoplogic * aform annoted list
  | AFforall of aquant_form annoted
  | AFexists of aquant_form annoted
  | AFlet of (Symbols.t * Ty.t) list * Symbols.t * aterm * aform annoted
  | AFnamed of Hstring.t * aform annoted

type atyped_decl = 
  | AAxiom of loc * string * aform
  | ARewriting of loc * string * ((aterm rwt_rule) annoted) list
  | AGoal of loc * string * aform annoted
  | ALogic of loc * string list * plogic_type
  | APredicate_def of loc * string * (string * ppure_type) list * aform
  | AFunction_def 
      of loc * string * (string * ppure_type) list * ppure_type * aform
  | ATypeDecl of loc * string list * string * body_type_decl


type annoted_node =
  | AD of (atyped_decl annoted * Why_typing.env)
  | AF of aform annoted * aform annoted option
  | AT of aterm annoted
  | QF of aquant_form annoted


module MDep : (Map.S with type key = atyped_decl annoted)



type env = {
  buffer : sbuffer;
  inst_buffer : sbuffer;
  errors : error_model;
  st_ctx : GMisc.statusbar_context;
  mutable ast : (atyped_decl annoted * Why_typing.env)list;
  mutable ctrl : bool;
  mutable last_tag : GText.tag;
  mutable search_tags : GText.tag list;
  mutable proof_tags : GText.tag list;
  mutable proof_toptags : GText.tag list;
  mutable start_select : int option;
  mutable stop_select : int option;
  dep : (atyped_decl annoted list * atyped_decl annoted list) MDep.t
}

val indent_size : int
val monospace_font : Pango.font_description
val general_font : Pango.font_description

val create_env :
  sbuffer -> 
  sbuffer ->
  error_model ->
  GMisc.statusbar_context ->
  (atyped_decl annoted * Why_typing.env) list -> 
  (atyped_decl annoted list * atyped_decl annoted list) MDep.t ->
  env

val find : 
  GText.tag -> sbuffer -> (atyped_decl annoted * Why_typing.env) list -> 
  annoted_node option

val find_decl : 
  GText.tag -> sbuffer -> (atyped_decl annoted * Why_typing.env) list -> 
  annoted_node option

val find_tag_inversedeps :
  (atyped_decl annoted list * atyped_decl annoted list) MDep.t ->
  GText.tag -> atyped_decl annoted list option

val find_tag_deps : 
  (atyped_decl annoted list * atyped_decl annoted list) MDep.t ->
  GText.tag -> atyped_decl annoted list option

val make_dep :
  (atyped_decl annoted  * Why_typing.env) list ->
  (atyped_decl annoted list * atyped_decl annoted list) MDep.t

val tag : sbuffer -> GText.tag 

val new_annot : sbuffer -> 'a -> int -> GText.tag -> 'a annoted

val annot : 
  sbuffer -> ((int tdecl, int) Why_ptree.annoted * Why_typing.env) list -> 
  (atyped_decl annoted * Why_typing.env) list

val annot_of_tterm : 
  sbuffer -> (int tterm, int) Why_ptree.annoted -> aterm annoted

val add_aaterm_list_at : sbuffer ->
  GText.tag list -> GText.iter -> string -> aterm annoted list -> unit

val add_aaform : error_model -> sbuffer -> int -> GText.tag list ->
  aform annoted -> unit

val to_ast : 
  (atyped_decl annoted * Why_typing.env) list -> 
  (int tdecl, int) Why_ptree.annoted list

val add_to_buffer : 
  error_model -> sbuffer -> (atyped_decl annoted * Why_typing.env) list -> unit

val print_typed_decl_list  :
  Format.formatter -> (int tdecl, int) Why_ptree.annoted list -> unit

val findtags_using : 
  atyped_decl -> (atyped_decl annoted * Why_typing.env) list -> GText.tag list 

val findtags_dep : 
  aterm -> (atyped_decl annoted * Why_typing.env) list -> GText.tag list 

val findtags_proof : 
  Explanation.t -> (atyped_decl annoted * Why_typing.env) list ->
  GText.tag list * GText.tag list 

val find_line : 
  int -> (atyped_decl annoted * 'a) list -> int * GText.tag
