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

open Unix

type kind =
  | Time_Sat
  | Time_Match
  | Time_CC
  | Time_Arith
  | Time_Arrays
  | Time_Sum
  | Time_Records
  | Time_Ac

type timer = {
  mutable u : float;
  mutable cpt: float;
}

type t = (kind, timer) Hashtbl.t 


let start_t t = t.u <- (times()).tms_utime

let pause_t t = t.cpt <- t.cpt +. ((times()).tms_utime -. t.u)

let get_t t = t.cpt



let init () =
  let h = Hashtbl.create 8 in
  Hashtbl.add h Time_Sat { u = 0.0; cpt = 0.0 };
  Hashtbl.add h Time_Match { u = 0.0; cpt = 0.0 };
  Hashtbl.add h Time_CC { u = 0.0; cpt = 0.0 };
  Hashtbl.add h Time_Arith { u = 0.0; cpt = 0.0 };
  Hashtbl.add h Time_Arrays { u = 0.0; cpt = 0.0 };
  Hashtbl.add h Time_Sum { u = 0.0; cpt = 0.0 };
  Hashtbl.add h Time_Records { u = 0.0; cpt = 0.0 };
  Hashtbl.add h Time_Ac { u = 0.0; cpt = 0.0 };
  h



let pause h t = pause_t (Hashtbl.find h t)

let pause_all h =  Hashtbl.iter (fun _ it -> pause_t it)

let start h t = 
  Hashtbl.iter (fun x it -> 
    if x = t then start_t it else pause_t it)

let pause_and_restart h t f =
  pause h t;
  f ();
  start h t

let get h t = get_t (Hashtbl.find h t)
