(**************************************************************************)
(*                                                                        *)
(*     The Alt-ergo theorem prover                                        *)
(*     Copyright (C) 2006-2009                                            *)
(*                                                                        *)
(*     Sylvain Conchon                                                    *)
(*     Evelyne Contejean                                                  *)
(*     Stephane Lescuyer                                                  *)
(*     Mohamed Iguernelala                                                *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

{

  open Format


  let string_buf = Buffer.create 1024

  let preftab = Hashtbl.create 17 

  let prefix = ref "test"
		
  let filenum = ref 0

  let name = ref "alt-ergo"

  let exi = ref ""
  let obj = ref ""
  let cobj = ref ""
  let ares = ref "Valid"

  let flags= [Open_text; Open_excl; Open_creat]

  let new_prefix str= 
    Hashtbl.add preftab !prefix !filenum;
    prefix := str;
    filenum :=  
    try Hashtbl.find preftab str with
	Not_found -> 0

  let prefixe = ref ""

  let newfile () = 
    let s = Printf.sprintf "%03d" !filenum in
    ("testfile-"^ !prefix^s^".mlw")

  let rec split_char sep str =
    try
      let i = String.index str sep in
      String.sub str 0 i ::
	split_char sep (String.sub str (i+1) (String.length str - i - 1))
    with Not_found ->
      [str]

  let write str = 
    incr filenum;
    while Sys.file_exists (newfile ()) do incr filenum done;
    let fname = newfile () in
    let chan=open_out fname in
    output_string chan str;
    flush chan;
    close_out chan;
    fname
      
  let out_tex =
      open_out_gen [Open_creat; Open_trunc; Open_append] 0o666 "results.tex"
  let fmt_tex = formatter_of_out_channel out_tex


  let init_sec n =
    fprintf fmt_tex "\\subsection{%s}\n@." n
    
  let sec_command fname =
    fprintf fmt_tex "\\subsubsection{Commande exécutée}\n\n";
    fprintf fmt_tex "\\begin{verbatim}\n";
    fprintf fmt_tex "%s %s\n" !name fname;
    fprintf fmt_tex "\\end{verbatim}\n@."
    
  let sec_exigence s =
    let refs = split_char ',' s in
    fprintf fmt_tex 
      "\\subsubsection{Référence de l\'exigence fonctionnelle}\n\n";
    fprintf fmt_tex "\\begin{itemize}\n";
    List.iter (fun r ->
      fprintf fmt_tex "\\item %s \n" r;
    ) refs;
    fprintf fmt_tex "\\end{itemize}\n@."

  let sec_obj obj =
    fprintf fmt_tex "\\subsubsection{Objectif(s) du test}\n\n";
    fprintf fmt_tex "%s\\\\\n" !cobj;
    fprintf fmt_tex "%s\n" obj

  let sec_desc code =
    fprintf fmt_tex "\\subsubsection{Description du test}\n\n";
    fprintf fmt_tex "\\begin{verbatim}\n";
    fprintf fmt_tex "%s\n" code;
    fprintf fmt_tex "\\end{verbatim}\n@."
    

  let sec_res ares ok =
    fprintf fmt_tex "\\subsubsection{Résultat attendu}\n\n";
    fprintf fmt_tex "%s.\n" ares;
    fprintf fmt_tex "\n\\bigskip\n\n";
    fprintf fmt_tex "Résultat du test : \\textbf{%s}\n@." 
      (if ok then "OK" else "KO")
  

}

let file = ([^'$'])+
let sep = '$'
let pref = "$$$"
let exi = "$exi:"
let obj = "$obj:"
let cobj = "$cobj:"
let ares = "$res:"
let comment = "$$" [^'\n']* ( '\n' | eof ) 
let alpha= [ 'a'-'z' 'A'-'Z' ]
let ident= (alpha | '_' | '-')+

rule split = parse
    pref (ident as newpref) ' '* '\n' { new_prefix newpref; true }
  | exi (file as f) { exi := f; true }
  | obj  (file as f) { obj := f; true }
  | cobj (file as f) { cobj := f; true }
  | ares  (file as f) '\n' { ares := f; true }
  | file {
    let code = (Lexing.lexeme lexbuf) in
    let fname = write code in
    let ok =
      if !ares = "Incorrect" then 
	Sys.command(sprintf "%s %s" !name fname) <> 0
      else
	Sys.command(sprintf "%s %s | grep -q -w %s" !name fname !ares) = 0
    in
    init_sec fname;
    sec_command fname;
    sec_exigence !exi;
    sec_obj !obj;
    sec_desc code;
    sec_res !ares ok;
    true
  }
  | sep { true }
  | comment { true }
  | eof { false }
  | _ { failwith "????"}

{
  let cwd=Sys.getcwd ()

  let process file =
    Sys.chdir cwd;
    let chan=open_in file in
    Sys.chdir (Filename.dirname file);
    let buf=Lexing.from_channel chan in
    while split buf do () done;
    close_in chan
      
  let _ = Arg.parse 
    ["-n", Arg.Set_string name, "<name> the command line for Alt-Ergo"] 
    process "file splitter for tests";
    Sys.chdir cwd

}
