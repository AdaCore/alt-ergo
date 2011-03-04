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

  let string_buf=Buffer.create 1024

  let preftab= Hashtbl.create 17 

  let prefix= ref "test"
		
  let filenum= ref 0

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

  let write str = 
    incr filenum;
    while Sys.file_exists (newfile ()) do incr filenum done;
    let chan=open_out (newfile ()) in
      output_string chan str;
      flush chan;
      close_out chan
}

let file = ([^'$'])+
let sep = '$'
let pref = "$$$"
let comment = "$$" [^'\n']* ( '\n' | eof ) 
let alpha= [ 'a'-'z' 'A'-'Z' ]
let ident= (alpha | '_')+

rule split = parse
    pref (ident as newpref) ' '* '\n' { new_prefix newpref; true }
  | file { write (Lexing.lexeme lexbuf);true }
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
      
  let _ = Arg.parse [] process "file splitter for tests"; Sys.chdir cwd

}
