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

open Format
open Why_ptree

(* not quite ''pretty''-printing, but helps for quick debugging *)

let rec print_term fmt t = 
  print_term_desc fmt t.c.tt_desc
and print_term_desc fmt =  function
  | TTconst Ttrue -> fprintf fmt "true"
  | TTconst Tfalse -> fprintf fmt "false"
  | TTconst Tint s -> fprintf fmt "%s" s
  | TTconst Treal s -> fprintf fmt "%s" (Num.string_of_num s)
  | TTvar x -> Symbols.print fmt x
  | TTinfix(t1,op,t2) -> 
      fprintf fmt "%a%a%a" print_term t1 Symbols.print op print_term t2
  | TTapp(f,l) -> 
      fprintf fmt "%a(%a)" Symbols.print f print_term_list l
  | _ -> failwith "not implemented"
and print_term_list fmt = List.iter (fprintf fmt "%a," print_term)

let rec print_atom fmt a = match a.c with
  | TAtrue -> fprintf fmt "@true"
  | TAfalse -> fprintf fmt "@false"
  | TAeq tl -> fprintf fmt "=(%a)" print_term_list tl
  | TAneq tl -> fprintf fmt "<>(%a)" print_term_list tl
  | TAdistinct tl -> fprintf fmt "distinct(%a)" print_term_list tl
  | TAle tl -> fprintf fmt "<=(%a)" print_term_list tl
  | TAlt tl -> fprintf fmt "<(%a)" print_term_list tl
  | TApred t -> fprintf fmt "%a" print_term t 
  | TAbuilt(s, tl) -> fprintf fmt "%s(%a)" (Hstring.view s) print_term_list tl

let print_op fmt = function
  | OPand -> fprintf fmt "/\\"
  | OPor -> fprintf fmt "\\/"
  | OPimp -> fprintf fmt "=>"
  | OPnot -> fprintf fmt "~"
  | OPif t -> fprintf fmt "if (%a) " print_term t
  | OPiff -> fprintf fmt "<=>"

let rec print_form fmt f = match f.c with
  | TFatom a -> fprintf fmt "%a" print_atom a
  | TFop (op,tl) -> fprintf fmt "%a(%a)" print_op op print_form_list tl
  | TFforall qf -> fprintf fmt "forall ..., %a" print_form qf.qf_form
  | TFexists qf -> fprintf fmt "exists ..., %a" print_form qf.qf_form
  | TFlet (up,var,t,f) -> fprintf fmt "let ..., %a" print_form f
  | TFnamed(lbl, f) -> fprintf fmt "%s:%a" (Hstring.view lbl) print_form f
and print_form_list fmt = List.iter (fprintf fmt "%a," print_form)


(**********************************************)
(***** print all structure inside formula *****)
(**********************************************)

let rec print_ppure_type fmt = function
  | PPTunit -> fprintf fmt "unit"
  | PPTint -> fprintf fmt "int"
  | PPTbool -> fprintf fmt "bool"
  | PPTreal -> fprintf fmt "real"
  | PPTbitv size -> fprintf fmt "bitv[%d]" size
  | PPTvarid (s, loc) -> fprintf fmt "\'%s" s
  (* | PPTfarray pp -> fprintf fmt "%a farray" print_ppure_type pp *)
  | PPTexternal ([], s, loc) ->
      fprintf fmt "%s" s
  | PPTexternal (pptypes, s, loc) ->
      fprintf fmt "%a %s" (print_ppure_type_list true) pptypes s

and print_ppure_type_list nested fmt l =
  let rec aux fmt = function
    | [] -> ()
    | [p] -> print_ppure_type fmt p
    | p::r -> fprintf fmt "%a,%a" print_ppure_type p aux r
  in
  if not nested then aux fmt l
  else match l with
    | [] -> ()
    | [s] -> aux fmt l
    | s::r -> fprintf fmt "(%a)" aux l

let print_plogic_type fmt = function
  | PPredicate [] -> fprintf fmt "prop"
  | PPredicate pptl -> 
      fprintf fmt "%a -> prop" (print_ppure_type_list false) pptl
  | PFunction ([], ppt) ->
    fprintf fmt "%a" print_ppure_type ppt
  | PFunction (pptl, ppt) ->
      fprintf fmt "%a -> %a" (print_ppure_type_list false) pptl 
    print_ppure_type ppt


let print_tconstant fmt = function
  | Tvoid -> fprintf fmt "void"
  | Ttrue -> fprintf fmt "true"
  | Tfalse -> fprintf fmt "false"
  | Tint s -> fprintf fmt "%s" s
  | Treal n ->
    let str = (Num.string_of_num n) in
    if String.contains str '.' then
      fprintf fmt "%s" str
    else
      fprintf fmt "%s.0" str
  | Tbitv s -> fprintf fmt "%s" s

let tconstant_to_string = function
  | Tvoid -> "void"
  | Ttrue -> "true"
  | Tfalse -> "false"
  | Tint s -> s
  | Treal n -> Num.string_of_num n
  | Tbitv s -> s

let rec print_var_list fmt var_list is_forall = 
    if (is_forall) then
    match var_list with
    | [] -> ()
    | [s,ty] -> fprintf fmt "forall %a:%a " Symbols.print s Ty.print ty
    | (s,ty)::l ->
        fprintf fmt "forall %a:%a. %a" Symbols.print s Ty.print ty print_var_list2 l
    else 
    match var_list with
    | [] -> ()
    | [s,ty] -> fprintf fmt "%a:%a" Symbols.print s Ty.print ty
    | (s,ty)::l ->
        fprintf fmt "%a:%a,%a" Symbols.print s Ty.print ty print_var_list3 l
and print_var_list2 fmt var_list = print_var_list fmt var_list true
and print_var_list3 fmt var_list = print_var_list fmt var_list false

let rec print_string_sep sep fmt = function
  | [] -> ()
  | [s] -> fprintf fmt "%s" s
  | s::r -> fprintf fmt "%s%s%a" s sep (print_string_sep sep) r

let rec print_string_list fmt = print_string_sep "," fmt

let print_astring_list fmt l =
  let rec aux fmt = function
    | [] -> ()
    | [s] -> fprintf fmt "\'%s" s
    | s::r -> fprintf fmt "\'%s,%a" s aux r
  in
  match l with
    | [] -> ()
    | [s] -> aux fmt l
    | s::r -> fprintf fmt "(%a)" aux l

let rec print_string_ppure_type_list fmt = function
  | [] -> ()
  | [s,ppt] -> fprintf fmt "%s:%a" s print_ppure_type ppt
  | (s,ppt)::l -> fprintf fmt "%s:%a,%a" s print_ppure_type ppt
      print_string_ppure_type_list l

let print_pred_type_list fmt = function
  | [] -> ()
  | l -> fprintf fmt "(%a)" print_string_ppure_type_list l

(**************** get free variable in formula *******************)

let uniq_pair lst_pair = 
  List.fold_left (fun acc pair -> if List.length acc = 0 then [pair] else
      begin
        if List.exists (fun p -> fst pair = fst p) acc then
          acc
        else
          pair :: acc
      end
    ) [] lst_pair
      
let rec get_free_var_term_list is_pred lst = match lst with
    | [] -> []
    | h :: t -> (get_free_var_term is_pred h) @ (get_free_var_term_list is_pred t)

and get_free_var_term is_pred term = 
    match term.c.tt_desc with
    | TTconst c -> []
    | TTvar sym -> 
        if (is_pred) then
            []
        else
            [(sym, term.c.tt_ty)]
    | TTapp (s, term_list) ->
        if (is_pred) then
            (s, term.c.tt_ty) :: get_free_var_term_list is_pred term_list
        else
            get_free_var_term_list is_pred term_list
    | TTinfix (t1, s, t2) ->
    ((get_free_var_term is_pred t1) @ (get_free_var_term is_pred t2))
    | TTprefix (s, t) -> get_free_var_term is_pred t
    | TTget (t1, t2) | TTconcat (t1, t2)
         -> (get_free_var_term is_pred t1) @ (get_free_var_term is_pred t2)
    | TTset (t1, t2, t3) | TTextract (t1, t2, t3)
         -> (get_free_var_term is_pred t1) @ (get_free_var_term is_pred t2) @ 
        (get_free_var_term is_pred t3)
    | TTdot (t, str) -> get_free_var_term is_pred t
    | TTrecord term_list -> 
      get_free_var_term_list is_pred (List.map snd term_list)
    | TTlet (s, t1, t2) -> 
      (get_free_var_term is_pred t1) @ (get_free_var_term is_pred t2)
    | TTnamed (str, t) -> get_free_var_term is_pred t

let get_free_var_atom is_pred a = match a.c with
    | TAtrue | TAfalse -> []
    | TAeq terms | TAdistinct terms | TAneq terms 
    | TAle terms | TAlt terms -> get_free_var_term_list is_pred terms
    | TApred term -> get_free_var_term is_pred term
    | TAbuilt (_, _) -> 
      Printf.printf "\n[get_free_var_atom] TAbuilt not implemented\n"; []

let rec get_free_var_tf is_pred formula = match formula.c with
    | TFatom a -> get_free_var_atom is_pred a
    | TFop (_, lst_tf) -> get_free_var_tf_list is_pred lst_tf
    | TFforall { qf_bvars = bv; qf_upvars = uv; qf_form = tf }
    | TFexists { qf_bvars = bv; qf_upvars = uv; qf_form = tf } ->
        let free_var = get_free_var_tf is_pred tf in
        let closed_var = (List.map fst bv) in
            List.filter (fun (v, _) -> not (List.mem v closed_var)) free_var
    | TFlet (_, _, _, _) -> printf "[get_free_var_tf] TFlet not implemented"; []
    | TFnamed (_, _) -> printf "[get_free_var_tf] TFnamed not implemented"; []

and get_free_var_tf_list is_pred lst = match lst with 
    | [] -> []
    | h :: t -> (get_free_var_tf is_pred h) @ (get_free_var_tf_list is_pred t)

let get_free_var_form is_pred tf = 
  let lst = get_free_var_tf is_pred tf in
    lst

let get_preds_or_free_var is_pred decl = match decl.c with
    | TAxiom(_, s, _, tf) -> get_free_var_form is_pred tf
    | TGoal(_, _, s, tf) -> get_free_var_form is_pred tf
    | TPredicate_def(_, _, _, tf) -> get_free_var_form is_pred tf
    | TFunction_def(_, _, _, _, tf) -> get_free_var_form is_pred tf
    | _ -> []

let get_free_var decl = uniq_pair (get_preds_or_free_var false decl)

(**************** to delete *******************)


let rec print_tterm fmt {Why_ptree.c= {tt_desc = tt_desc; tt_ty = tpe}} =
    print_tt_desc fmt tpe tt_desc

and print_tterm_list se fmt = function
  | [] -> ()
  | [t] -> print_tterm fmt t
  | t::r -> fprintf fmt "%a%s%a" print_tterm t se (print_tterm_list se) r

and print_record se fmt = function
  | [] -> ()
  | [c,t] -> fprintf fmt "%s = %a" (Hstring.view c) print_tterm t
  | (c,t)::r -> 
      fprintf fmt "%s = %a%s%a" (Hstring.view c) 
    print_tterm t se (print_record se) r


and print_tt_desc fmt tpe = function
  | TTconst c -> print_tconstant fmt c
  | TTvar s -> 
    (* fprintf fmt "[";Ty.print fmt tpe;fprintf fmt "]-"; *)
    Symbols.print fmt s
  | TTapp (f, ts) ->
      (* fprintf fmt "{";Ty.print fmt tpe;fprintf fmt "}-"; *)
      fprintf fmt "%a(%a)" Symbols.print f (print_tterm_list ",") ts
  | TTinfix (t1, s, t2) ->
      fprintf fmt "(%a %a %a)" print_tterm t1 Symbols.print s print_tterm t2
  | TTprefix (s, t) ->
      fprintf fmt "%a %a" Symbols.print s print_tterm t
  | TTlet (s, t1, t2) ->
      fprintf fmt "let %a = %a in %a"
    Symbols.print s print_tterm t1 print_tterm t2
  | TTconcat (t1, t2) ->
      fprintf fmt "%a@%a" print_tterm t1 print_tterm t2
  | TTextract (t, t1, t2) -> 
      fprintf fmt "%a^{%a;%a}" print_tterm t print_tterm t1 print_tterm t2
  | TTset (t, t1, t2) ->
      fprintf fmt "%a[%a<-%a]" print_tterm t print_tterm t1 print_tterm t2
  | TTget (t, t1) ->
      fprintf fmt "%a[%a]" print_tterm t print_tterm t1
  | TTdot (t, c) ->
      fprintf fmt "%a.%s" print_tterm t (Hstring.view c)
  | TTrecord r -> fprintf fmt "{ %a }" (print_record ";") r
  | TTnamed (lbl, t) -> fprintf fmt "%s:%a" (Hstring.view lbl) print_tterm t

let print_tatom fmt a = match a.Why_ptree.c with
  | TAtrue -> fprintf fmt "true" 
  | TAfalse -> fprintf fmt "false"
  | TAeq tl -> print_tterm_list " = " fmt tl
  | TAneq tl -> print_tterm_list " <> " fmt tl
  | TAdistinct tl ->
      fprintf fmt "distinct(%a)" (print_tterm_list ",") tl
  | TAle tl -> print_tterm_list " <= " fmt tl
  | TAlt tl -> print_tterm_list " < " fmt tl
  | TApred t -> print_tterm fmt t
  | TAbuilt (h, tl) -> print_tterm_list (" "^(Hstring.view h)^" ") fmt tl

let print_oplogic fmt = function
  | OPand -> fprintf fmt "and"
  | OPor -> fprintf fmt "or"
  | OPimp -> fprintf fmt "->"
  | OPnot -> fprintf fmt "not"
  | OPif t -> fprintf fmt "%a ->" print_tterm t
  | OPiff -> fprintf fmt "<->"

let is_op_imp_iff = function
    | OPimp | OPiff -> true
    | _ -> false

let print_rwt fmt { rwt_vars = rv; rwt_left = rl; rwt_right = rr } =
  fprintf fmt "forall %a. %a = %a" 
    print_var_list3 rv print_tterm rl print_tterm rr

let rec print_rwt_list fmt = function
  | [] -> ()
  | [rwt] -> print_rwt fmt rwt
  | rwt::l -> fprintf fmt "%a; %a" print_rwt rwt print_rwt_list l

let rec print_quant_form fmt
  {qf_bvars = bv; qf_upvars = uv; qf_triggers = trs; qf_form = tf } is_forall =
    if is_forall then
      if List.length trs <> 0 then
        fprintf fmt "%a [%a]. %a" print_var_list2 bv 
          print_triggers trs print_tform tf
      else
        fprintf fmt "%a. %a" print_var_list2 bv print_tform tf
    else
        fprintf fmt "%a. %a" print_var_list3 bv print_tform tf

and print_quant_form2 fmt qf = print_quant_form fmt qf true
and print_quant_form3 fmt qf = print_quant_form fmt qf false

and print_triggers fmt = function
  | [] -> ()
  | [ts] -> print_tterm_list "," fmt ts
  | ts::l -> fprintf fmt "%a | %a" (print_tterm_list ",") ts print_triggers l

and print_tform2 fmt f = match f.Why_ptree.c with
  | TFatom a -> print_tatom fmt a
  | TFop (OPnot, [tf]) -> fprintf fmt "not (%a)" print_tform tf 
  | TFop (op, tfl) -> print_tform_list op fmt tfl
  | TFforall qf -> fprintf fmt "(%a)" print_quant_form2 qf
  | TFexists qf -> fprintf fmt "(exists %a)" print_quant_form3 qf
  | TFlet (vs, s, t, tf) -> 
      fprintf fmt "let %a = %a in\n %a" 
    Symbols.print s print_tterm t print_tform tf
  | TFnamed (_, tf) -> fprintf fmt "TFnamed - %a\n" print_tform tf

and print_tform fmt f = fprintf fmt " %a" print_tform2 f

and print_tform_list op fmt = function
  | [] -> ()
  | [tf] -> print_tform fmt tf
  | tf::l -> 
        if (is_op_imp_iff op) then
        fprintf fmt "((%a) %a (%a))"
        print_tform tf print_oplogic op (print_tform_list op) l
        else
        fprintf fmt "((%a) %a (%a))"
        print_tform tf print_oplogic op (print_tform_list op) l

let rec print_record_type fmt = function
  | [] -> ()
  | [c, ty] -> fprintf fmt "%s : %a" c print_ppure_type ty
  | (c, ty)::l -> 
      fprintf fmt "%s : %a; %a" c print_ppure_type ty print_record_type l

let extract_second_pred tf = match tf.c with
    | TFforall {qf_form = {c = TFop (OPiff, tf_lst)}} -> 
      List.hd (List.tl tf_lst)
    | _ -> failwith "matching error in extract_second_pred"

let extract_second_func tf = match tf.c with
    | TFforall {qf_form = {c = TFatom {c = TAeq term_lst}}} -> 
      List.hd (List.tl term_lst)
    | _ -> failwith "matching error in extract_second_pred"

let print_typed_decl fmt td = match td.Why_ptree.c with
  | TAxiom (_, s, inv, tf) -> 
    if (String.get s 0 = '@') then
      let new_name = String.sub s 1 ((String.length s) - 1) in
      fprintf fmt "axiom %s : %a" new_name print_tform tf
    else
      fprintf fmt "axiom %s : %a" s print_tform tf
            
  | TRewriting (_, s, rwtl) -> 
    fprintf fmt "rewriting %s : %a" s print_rwt_list rwtl
  | TGoal (_, _, s, tf) -> 
    fprintf fmt "goal %s : not(%a)" s print_tform tf
  | TLogic (_, ls, ty) ->
    fprintf fmt "logic %a : %a" print_string_list ls print_plogic_type ty
  | TPredicate_def (_, p, spptl, tf) ->
    fprintf fmt "predicate %s %a = (%a)" p 
            print_pred_type_list spptl print_tform (extract_second_pred tf)
  | TFunction_def (_, f, spptl, ty, tf) ->
    fprintf fmt "function %s (%a) : %a = %a" f 
      print_string_ppure_type_list spptl print_ppure_type ty 
      print_tterm (extract_second_func tf)
  | TTypeDecl (_, ls, s, Abstract) ->
      fprintf fmt "type %a %s" print_astring_list ls s
  | TTypeDecl (_, ls, s, Enum lc) -> 
    fprintf fmt "type %a %s = %a" print_astring_list ls s 
      (print_string_sep " | ") lc
  | TTypeDecl (_, ls, s, Record rt) -> 
    fprintf fmt "type %a %s = %a" print_astring_list ls s print_record_type rt 

let print_tdcl_lst fmt decl_lst =
  List.iter (fprintf fmt "%a\n@." print_typed_decl) decl_lst

let print_typed_decl_list fmt ?(same_order = true) decl_lst =
  let all_logic_decl = ref [] in
  let (hypothesis, other_rules) = List.partition (fun d -> match d.c with 
        | TAxiom (_, name, _, body) -> (String.get name 0) = '@'
        | TLogic (_, str_lst, _) -> 
          all_logic_decl := !all_logic_decl @ str_lst; false
        | _ -> false 
    ) decl_lst in
  let (goals, rest_of_rules) = List.partition (fun d -> match d.c with 
        | TGoal _ -> true
        | _ -> false 
    ) other_rules in

  if same_order then
    print_tdcl_lst fmt rest_of_rules
  else
    begin
      let (types, lgocis_axioms) = List.partition (fun decl -> match decl.c with 
        | TTypeDecl (_,_,_,_) -> true | _ -> false) rest_of_rules in
      let (logics, axioms) = List.partition (fun decl -> match decl.c with 
        | TLogic (_,_,_) -> true | _ -> false) lgocis_axioms in
      print_tdcl_lst fmt types;
      print_tdcl_lst fmt logics;
      print_tdcl_lst fmt axioms
    end;    
  
  let free_var_in_hyps = uniq_pair (List.flatten (List.map 
    (fun decl -> get_free_var decl) hypothesis)) in
    fprintf fmt "@.";
    (List.iter
        (fun (v, tpe) ->
          let var_name = Symbols.to_string v in
          if not (List.mem var_name !all_logic_decl) then
            fprintf fmt "logic %s: %a@." var_name Ty.print tpe)
        free_var_in_hyps);
               
  fprintf fmt "@.";  
  print_tdcl_lst fmt hypothesis;
  print_tdcl_lst fmt goals;

(**********************************************)
