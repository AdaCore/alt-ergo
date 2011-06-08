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
  let tex_file = ref "results.tex"

  let exi = ref ""
  let obj = ref ""
  let cobj = ref ""
  let ares = ref "Valid"

  let results_table = ref []
  let exi_tests = ref []
  
  let green s =
    sprintf "[1;32m%s[1;0m" s
    
  let red s =
    sprintf "[1;31m%s[1;0m" s

  let ko_str = red "*KO"
  let ok_str = green "OK"

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


  let escu str =
    String.concat "\\_" (split_char '_' str)

  let rec remove_trailing_whitespaces_end str =
    if String.length str > 0 && 
      (str.[String.length str - 1] = '\n' 
	  || str.[String.length str - 1] = ' '
	  || str.[String.length str - 1] = '\t')  then
      remove_trailing_whitespaces_end (String.sub str 0 (String.length str - 1))
    else str

  let rec remove_trailing_whitespaces_begin str =
    if String.length str > 0 && 
      (str.[0] = '\n' || str.[0] = ' ' || str.[0] = '\t')  then
      remove_trailing_whitespaces_begin 
	(String.sub str 1 (String.length str - 1))
    else str

  let rec remove_trailing_whitespaces str =
    remove_trailing_whitespaces_end (remove_trailing_whitespaces_begin str)

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
      open_out_gen [Open_creat; Open_trunc; Open_append] 0o666 !tex_file
  let fmt_tex = formatter_of_out_channel out_tex


  let init_sec n =
    fprintf fmt_tex "\\subsection{%s}\n@." (escu n)
    
  let sec_command fname =
    fprintf fmt_tex "\\subsubsection{Commande exécutée}\n\n";
    fprintf fmt_tex "\\begin{verbatim}\n";
    fprintf fmt_tex "%s %s\n" !name fname;
    fprintf fmt_tex "\\end{verbatim}\n@."
    
  let sec_exigence s fname =
    let refs = split_char ',' s in
    fprintf fmt_tex 
      "\\subsubsection{Référence de l\'exigence fonctionnelle}\n\n";
    fprintf fmt_tex "\\begin{itemize}\n";
    List.iter (fun r ->
      fprintf fmt_tex "\\item \\textsc{%s} \n" r;
      exi_tests := (r, fname)::!exi_tests
    ) refs;
    fprintf fmt_tex "\\end{itemize}\n@."

  let sec_obj obj =
    fprintf fmt_tex "\\subsubsection{Objectif(s) du test}\n\n";
    fprintf fmt_tex "%s\n\n" !cobj;
    fprintf fmt_tex "%s\n" obj

  let sec_desc code =
    fprintf fmt_tex "\\subsubsection{Description du test}\n\n";
    fprintf fmt_tex "\\begin{verbatimgray}\n";
    fprintf fmt_tex "%s\n" code;
    fprintf fmt_tex "\\end{verbatimgray}\n@."
    

  let sec_res ares ok =
    fprintf fmt_tex "\\subsubsection{Résultat attendu}\n\n";
    fprintf fmt_tex "%s.\n" ares;
    fprintf fmt_tex "\n\\bigskip\n\n";
    fprintf fmt_tex "Résultat du test : \\textbf{%s}\n@." 
      (if ok then "OK" else "KO")
  
  let dump_exi_tests file =
    let out =
      open_out_gen [Open_creat; Open_trunc; Open_append] 0o666 file in
    let fmt = formatter_of_out_channel out in
    fprintf fmt "\\subsection{Éxigences fonctionnelles et tests}\n@.";
    fprintf fmt "\\begin{center}\\begin{longtable}{|p{0.5\\textwidth}|p{0.5\\textwidth}|}\n\\hline\n@.";
    List.iter (fun (ex, fname) ->
      fprintf fmt "\\textsc{%s} & %s \\\\\\hline\n" ex (escu fname)
    ) (List.sort (fun (e1, _) (e2, _) -> String.compare e1 e2) !exi_tests);
    fprintf fmt "\\end{longtable}\\end{center}\n@.";
    close_out out
    
  let dump_results_table file =
    let out =
      open_out_gen [Open_creat; Open_trunc; Open_append] 0o666 file in
    let fmt = formatter_of_out_channel out in
    fprintf fmt "\\subsection{Résultats des tests}\n@.";
    fprintf fmt "\\begin{center}\\begin{longtable}{|p{0.5\\textwidth}|p{0.5\\textwidth}|}\n\\hline\n@.";
    List.iter (fun (fname, ok) ->
      fprintf fmt "%s & %s \\\\\\hline\n" (escu fname) 
	(if ok then "OK" else "KO")
    ) (List.rev !results_table);
    fprintf fmt "\\end{longtable}\\end{center}\n@.";
    close_out out

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
  | cobj (file as f) { obj := ""; cobj := f; true }
  | ares  (file as f) '\n' { ares := f; true }
  | file {
    let code = remove_trailing_whitespaces (Lexing.lexeme lexbuf) in
    let fname = write code in
    let ok =
      if !ares = "Incorrect" then 
	Sys.command(sprintf "%s %s" !name fname) <> 0
      else if !ares = "Correct" then 
	Sys.command(sprintf "%s %s" !name fname) = 0
      else
	Sys.command(sprintf "%s %s | grep -q -w \"%s\"" !name fname !ares) = 0
    in
    init_sec fname;
    sec_command fname;
    sec_exigence !exi fname;
    sec_obj !obj;
    sec_desc code;
    sec_res !ares ok;
    if ok then print_endline (sprintf "%s  %s" fname ok_str)
    else print_endline (sprintf "%s %s" fname ko_str);
    results_table := (fname, ok)::!results_table;
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
    ignore (Sys.command("rm -f testfile-*.mlw"));
    let buf=Lexing.from_channel chan in
    while split buf do () done;
    let fres = Filename.chop_extension !tex_file in
    dump_exi_tests (fres ^ "_exi.tex");
    dump_results_table (fres ^ "_table.tex");
    close_in chan;
    close_out out_tex
      
  let _ = Arg.parse 
    ["-n", Arg.Set_string name, "<name> the command line for Alt-Ergo (default alt-ergo)";
     "-o", Arg.Set_string tex_file, "<file.tex> output LaTeX file (default results.tex)"]
    process "LaTeX tests report generator";
    Sys.chdir cwd

}
