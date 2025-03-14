(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) --- OCamlPro SAS                                     *)
(*                                                                        *)
(*     This file is distributed under the terms of OCamlPro               *)
(*     Non-Commercial Purpose License, version 1.                         *)
(*                                                                        *)
(*     As an exception, Alt-Ergo Club members at the Gold level can       *)
(*     use this file under the terms of the Apache Software License       *)
(*     version 2.0.                                                       *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     The Alt-Ergo theorem prover                                        *)
(*                                                                        *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                 *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout              *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

{
  [@@@ocaml.warning "-33"]
  open AltErgoLib
  open Options

  open Lexing
  open Native_parser

  let assoc_keyword =
    let tbl : (string, Native_parser.token) Hashtbl.t = Hashtbl.create 256 in
    let kw_list =
      [
        "ac"         , AC;
        "and"        , AND;
        "axiom"      , AXIOM;
        "bitv"       , BITV;
        "bool"       , BOOL;
        "case_split" , CASESPLIT;
        "check"      , CHECK;
        "check_sat"  , CHECK_SAT;
        "cut"        , CUT;
        "distinct"   , DISTINCT;
        "else"       , ELSE;
        "end"        , END;
        "exists"     , EXISTS;
        "extends"    , EXTENDS;
        "false"      , FALSE;
        "forall"     , FORALL;
        "function"   , FUNC;
        "goal"       , GOAL;
        "if"         , IF;
        "in"         , IN;
        "int"        , INT;
        "let"        , LET;
        "logic"      , LOGIC;
        "not"        , NOT;
        "or"         , OR;
        "xor"        , XOR;
        "predicate"  , PRED;
        "prop"       , PROP;
        "real"       , REAL;
        "rewriting"  , REWRITING;
        "then"       , THEN;
        "theory"     , THEORY;
        "true"       , TRUE;
        "type"       , TYPE;
        "unit"       , UNIT;
        "void"       , VOID;
        "match"      , MATCH;
        "with"       , WITH;
        "of"         , OF;
      ]
    in
    List.iter (fun (s, kw) -> Hashtbl.add tbl s kw) kw_list;
    fun tok -> Hashtbl.find tbl tok

  let mk_new_line lexbuf =
    let p = lexbuf.lex_curr_p in
    let p = { p with pos_lnum = p.pos_lnum + 1; pos_bol = p.pos_cnum } in
    lexbuf.lex_curr_p <- p

  let escaped_char = function
    | 'n' -> '\n'
    | 'r' -> '\r'
    | 't' -> '\t'
    | c -> c

  let n_zero, n_ten, n_16 = Numbers.Q.(from_int 0, from_int 10, from_int 16)

  let decimal_number s =
    let r = ref n_zero in
    for i=0 to String.length s - 1 do
      let c = Char.(code s.[i] - code '0') in
      r := Numbers.Q.(add (mult n_ten !r) (from_int c))
    done;
    !r

  let hexa_number s =
    let r = ref n_zero in
    for i=0 to String.length s - 1 do
      let c = s.[i] in
      let v =
        match c with
        | '0'..'9' -> Char.code c - Char.code '0'
        | 'a'..'f' -> Char.code c - Char.code 'a' + 10
        | 'A'..'F' -> Char.code c - Char.code 'A' + 10
        | _ -> assert false
      in
      r := Numbers.Q.(add (mult n_16 !r) (from_int v))
    done;
    !r

}

let alphabet = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let hexadecimal = digit | ['a'-'f''A'-'F']
let identifier = (alphabet | '_') (alphabet | '_' | digit | '?' | '\'')*

rule parse_token = parse
  | '\n'                     { mk_new_line lexbuf; parse_token lexbuf }
  | [' ' '\t' '\r']+         { parse_token lexbuf }
  | '?'                      { QM }
  | '?' identifier as id     { QM_ID id }
  | identifier as i          { try assoc_keyword i with Not_found -> ID i }
  | digit+ as s              { INTEGER s }

  | (digit+ as i) ("" as f) ['e' 'E'] (['-' '+']? as sign (digit+ as exp))
  | (digit+ as i) '.' (digit* as f)
      (['e' 'E'] (['-' '+']? as sign (digit+ as exp)))?
  | (digit* as i) '.' (digit+ as f)
      (['e' 'E'] (['-' '+']? as sign (digit+ as exp)))?
      (* decimal real literals *)
      {
        let v =
          match exp,sign with
          | Some exp,Some "-" ->
            Numbers.(Q.div (decimal_number (i^f))
              (Q.from_z (Z.power (Z.from_int 10) (int_of_string exp))))
          | Some exp,_ ->
            Numbers.(Q.mult (decimal_number (i^f))
              (Q.from_z (Z.power (Z.from_int 10) (int_of_string exp))))
          | None,_ -> decimal_number (i^f)
        in
        let v =
          Numbers.(Q.div v (Q.from_z (Z.power (Z.from_int 10)
            (String.length f))))
        in
        NUM v
      }

  (* hexadecimal real literals a la C99 (0x..p..) *)
  | "0x" (hexadecimal+ as e) ('.' (hexadecimal* as f))?
      ['p''P'] (['+''-']? as sign) (digit+ as exp)
      {
        let f = match f with None -> "" | Some f -> f in
        let v =
          match sign with
          | "-" ->
            Numbers.(Q.div (hexa_number (e^f))
              (Q.from_z (Z.power (Z.from_int 2) (int_of_string exp))))
          | _ ->
            Numbers.(Q.mult (hexa_number (e^f))
              (Q.from_z (Z.power (Z.from_int 2) (int_of_string exp))))
        in
        let v =
          Numbers.(Q.div v (Q.from_z (Z.power (Z.from_int 16)
            (String.length f))))
        in
        NUM v
      }
  | "(*"  { parse_comment lexbuf; parse_token lexbuf }
  | "'"   { QUOTE }
  | ","   { COMMA }
  | ";"   { PV }
  | "("   { LEFTPAR }
  | ")"   { RIGHTPAR }
  | ":"   { COLON }
  | "->"  { RIGHTARROW }
  | "<-"  { LEFTARROW }
  | "<->" { LRARROW }
  | "="   { EQUAL }
  | "<"   { LT }
  | "<="  { LE }
  | ">"   { GT }
  | ">="  { GE }
  | "<>"  { NOTEQ }
  | "+"   { PLUS }
  | "-"   { MINUS }
  | "*"   { TIMES }
  | "**." { POWDOT }
  | "**"  { POW }
  | "/"   { SLASH }
  | "%"   { PERCENT }
  | "@"   { AT }
  | "."   { DOT }
  | "#"   { SHARP }
  | "["   { LEFTSQ }
  | "]"   { RIGHTSQ }
  | "{"   { LEFTBR }
  | "}"   { RIGHTBR }
  | "|"   { BAR }
  | "^"   { HAT }
  | "|->" { MAPS_TO }
  | "\""  { parse_string (Buffer.create 1024) lexbuf }
  | eof   { EOF }
  | _ as c {
    let loc = (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf) in
    let s = "illegal character: " ^ String.make 1 c in
    Errors.error (Errors.Lexical_error (loc, s))
  }

and parse_comment = parse
  | "*)" { () }
  | "(*" { parse_comment lexbuf; parse_comment lexbuf }
  | '\n' { mk_new_line lexbuf; parse_comment lexbuf }
  | eof  {
    let loc = (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf) in
    Errors.error (Errors.Lexical_error (loc, "unterminated comment"))
  }
  | _    { parse_comment lexbuf }

and parse_string str_buf = parse
  | "\"" { STRING (Buffer.contents str_buf) }
  | "\\" (_ as c) {
    Buffer.add_char str_buf (escaped_char c);
    parse_string str_buf lexbuf
  }

  | '\n' {
    mk_new_line lexbuf;
    Buffer.add_char str_buf '\n';
    parse_string str_buf lexbuf
  }

  | eof  {
    let loc = (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf) in
    Errors.error (Errors.Lexical_error (loc, "unterminated string"))
  }

  | _ as c {
    Buffer.add_char str_buf c; parse_string str_buf lexbuf
  }

{

  module Parser : Parsers.PARSER_INTERFACE = struct

    let aux aux_fun token lexbuf =
      try
        let res = aux_fun token lexbuf in
        Parsing.clear_parser ();
        res
      with
      (* The --fixed-error flag makes menhir alias
         the exception Error to Parsing.Parse_error *)
      | Parsing.Parse_error ->
        let loc = (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf) in
        let lex = Lexing.lexeme lexbuf in
        Parsing.clear_parser ();
        Errors.error (Errors.Syntax_error (loc, lex))

    let file    = aux Native_parser.file_parser    parse_token
    let expr    = aux Native_parser.lexpr_parser   parse_token
    let trigger = aux Native_parser.trigger_parser parse_token
  end

  let register_native () =
    (*register this parser in Input_lang: 3 different extensions recognized *)
    let p = (module Parser : Parsers.PARSER_INTERFACE) in
    Parsers.register_parser ~lang:".ae" p
}
