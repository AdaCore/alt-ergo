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

type e = Dep of Formula.t | BJ of Formula.t

module ES = Set.Make(struct 
  type t = e 
  let compare e1 e2 = match e1,e2 with
    | Dep e1, Dep e2 -> Formula.compare e1 e2
    | Dep _, _ -> 1
    | BJ e1, BJ e2 -> Formula.compare e1 e2
    | BJ _, _ -> -1
end)

type t = ES.t option

let everything = None

let empty = Some (ES.empty)

let mem l = function
  | None -> true
  | Some s -> ES.mem (BJ l) s

let singleton ?(bj = true) l = 
  Some (ES.singleton (if bj then BJ l else Dep l))

let make_deps sf = 
  Some (Formula.Set.fold (fun l acc -> ES.add (BJ l) acc) sf ES.empty)

let union d1 d2 = match d1,d2 with
    None , _ | _ , None -> None
  | Some s1 , Some s2 -> Some (ES.union s1 s2)


let merge d1 d2 = d1

let remove f = function
  | None -> None
  | Some s when ES.mem (BJ f) s -> Some (ES.remove (BJ f) s)
  | _ -> raise Not_found
  (*
    let s', found = 
      ES.fold (fun e (acc, found) -> 
	match e with  
	  | BJ e' when (not found) && Formula.compare e' f = 0 -> acc, true
	  | _ -> (ES.add e acc), found
      ) s (ES.empty, false) in
    if found then Some s' else raise Not_found
  *)

let print fmt = function
  | None -> Format.fprintf fmt "{Everything}"
  | Some s -> 
      Format.fprintf fmt "[";
      ES.iter (fun e -> match e with 
	| Dep f -> Format.fprintf fmt "{Dep:%a}" Formula.print f
	| BJ f -> Format.fprintf fmt "{BJ:%a}" Formula.print f) s;
      Format.fprintf fmt "]"

let print_proof fmt = function
  | None -> Format.fprintf fmt "{Everything}"
  | Some s -> 
      ES.iter (fun e -> match e with 
	| (Dep f | BJ f) -> Format.fprintf fmt "  %a@." Formula.print f
	(* | BJ f  -> Format.fprintf fmt "  %a@." Formula.print f *)
      ) s

let ids_of = function
  | None -> None
  | Some s ->
    Some (ES.fold (fun e acc ->
      let id = match e with
	| Dep f | BJ f -> Formula.id f in
      id::acc) s [])

let formulas_of = function
  | None  -> Formula.Set.empty
  | Some s -> 
      ES.fold (fun e acc -> 
                 match e with 
	             Dep f | BJ f -> Formula.Set.add f acc
              )s Formula.Set.empty
