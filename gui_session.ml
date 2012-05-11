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

type action =
  | Prune of int
  | IncorrectPrune of int
  | Unprune of int
  | AddInstance of int * string * string list
  | AddTrigger of int * string list
  | LimitLemma of int * string

let resulting_ids = Hashtbl.create 17

let save actions ac = 
  (match ac with 
    | Prune id -> Format.eprintf "Prune %d@." id
    | IncorrectPrune id -> Format.eprintf "Incorrectprune %d@." id
    | Unprune id -> Format.eprintf "Unrune %d@." id
    | AddInstance (id, name, vars) -> ()
    | AddTrigger (id, trs) -> ()
    | LimitLemma (id, nb) -> ()
  );
  Stack.push ac actions


let read_actions = function
  | Some cin -> 
    begin
      try (input_value cin: action Stack.t)
      with End_of_file -> Stack.create ()
    end
  | None -> Stack.create ()
