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



  module SS = Set.Make(struct
    include String 
    let compare s1 s2 = if compare s1 s2 = 0 then 0 else -1
  end)

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

  let greenbg s =
    sprintf "[1;102m%s[1;0m" s
      
  let redbg s =
    sprintf "[1;101m%s[1;0m" s
      

  let ko_str = redbg "*KO"
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

  let remove_trailing_whitespaces str =
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
      


  (* Captures the output and exit status of a unix command : aux func*)
  let syscall cmd =
    (* fprintf std_formatter "syscall: %s@." cmd; *)
    let inc, outc, errc = Unix.open_process_full cmd (Unix.environment ()) in  
    let buf = Buffer.create 16 in
    let buferr = Buffer.create 16 in
    (try
       while true do
	 Buffer.add_channel buf inc 1
       done
     with End_of_file -> ());
    (try
       while true do
	 Buffer.add_channel buferr errc 1
       done
     with End_of_file -> ());
    let status = Unix.close_process_full (inc, outc, errc) in
    let s =  Buffer.contents buferr in
    let l = String.length s in
    let serr = if l > 0 then String.sub s 0 ((String.length s) - 1) else s in
    (Buffer.contents buf, status, serr)

  let is_zero_status = function
    | Unix.WEXITED n | Unix.WSIGNALED n | Unix.WSTOPPED n -> n = 0

  let scan_rules s =
    let rules = split_char '\n' s in
    List.fold_left (fun acc r ->
      try Scanf.sscanf r "[rule] %s %s@\n" 
	    (fun r info ->
	      if List.mem (r,info) acc then acc else (r,info)::acc)
      with Scanf.Scan_failure _ | End_of_file -> acc)
      [] rules


  let init_sec n fmt_tex =
    fprintf fmt_tex "\\subsection{%s}\n@." (escu n)
    
  let sec_command fname fmt_tex =
    fprintf fmt_tex "\\subsubsection*{Commande exécutée}\n\n";
    fprintf fmt_tex "\\begin{verbatim}\n";
    fprintf fmt_tex "%s %s\n" !name fname;
    fprintf fmt_tex "\\end{verbatim}\n@."
    
  let sec_exigence refs fname fmt_tex =
    fprintf fmt_tex 
      "\\subsubsection*{Référence de l\'exigence fonctionnelle}\n\n";
    fprintf fmt_tex "\\begin{itemize}\n";
    List.iter (fun (r,info) ->
      fprintf fmt_tex "\\item \\textsc{%s} \\verb|%s|\n" r info;
      exi_tests := (r, fname)::!exi_tests
    ) refs;
    fprintf fmt_tex "\\end{itemize}\n@."

  let sec_obj obj fmt_tex =
    fprintf fmt_tex "\\subsubsection*{Objectif(s) du test}\n\n";
    fprintf fmt_tex "%s\n\n" !cobj;
    fprintf fmt_tex "%s\n" obj

  let sec_desc code fmt_tex =
    fprintf fmt_tex "\\subsubsection*{Description du test}\n\n";
    fprintf fmt_tex "\\begin{verbatimgray}\n";
    fprintf fmt_tex "%s\n" code;
    fprintf fmt_tex "\\end{verbatimgray}\n@."
    

  let sec_res ares ok fmt_tex =
    fprintf fmt_tex "\\subsubsection*{Résultat attendu}\n\n";
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
    ) (List.stable_sort (fun (e1, _) (e2, _) -> String.compare e1 e2) 
	 (List.rev !exi_tests));
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

rule split fmt_tex = parse
    pref (ident as newpref) ' '* '\n' { new_prefix newpref; true }
  | exi (file as f) { exi := f; true }
  | obj  (file as f) { obj := f; true }
  | cobj (file as f) { obj := ""; cobj := f; true }
  | ares  (file as f) '\n' { ares := f; true }
  | file {
    let code = remove_trailing_whitespaces (Lexing.lexeme lexbuf) in
    let fname = write code in
    let answ, status, rules = syscall (sprintf "%s %s" !name fname) in
    let ok =
      if !ares = "Incorrect" then not (is_zero_status status)
      else if !ares = "Correct" then is_zero_status status
      else is_zero_status status && 
	Sys.command (sprintf "echo \"%s\" | grep -q -w \"%s\"" answ !ares) = 0
    in
    init_sec fname fmt_tex;
    sec_command fname fmt_tex;
    sec_exigence (scan_rules rules) fname fmt_tex;
    sec_obj !obj fmt_tex;
    sec_desc code fmt_tex;
    sec_res !ares ok fmt_tex;
    if ok then print_endline (sprintf "%s  %s" fname ok_str)
    else print_endline (sprintf "%s %s" (red fname) ko_str);
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
    let out_tex =
      open_out_gen [Open_creat; Open_trunc; Open_append] 0o666 !tex_file in
    let fmt_tex = formatter_of_out_channel out_tex in
    let buf=Lexing.from_channel chan in
    while split fmt_tex buf do () done;
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
