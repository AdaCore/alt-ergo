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
open Format

type kind =
  | TSat
  | TMatch
  | TCC
  | TArith
  | TArrays
  | TSum
  | TRecords
  | TAc

let print fmt = function 
  | TSat -> fprintf fmt "TSat"
  | TMatch -> fprintf fmt "TMatch"
  | TCC -> fprintf fmt "TCC"
  | TArith -> fprintf fmt "TArith"
  | TArrays -> fprintf fmt "TArrays"
  | TSum -> fprintf fmt "TSum"
  | TRecords -> fprintf fmt "TRecords"
  | TAc -> fprintf fmt "TAc"

type timer = {
  mutable u : float;
  mutable cpt: float;
  mutable active: bool;
  mutable paused: bool;
}

type t = (kind, timer) Hashtbl.t 


let start_t t cur = 
  if t.paused then t.u <- cur;
  t.active <- true;
  t.paused <- false

let pause_t t cur =
  if not t.paused then t.cpt <- t.cpt +. (cur -. t.u);
  t.paused <- true;
  t.active <- false

let pause_active_t t cur = 
  if not t.paused then t.cpt <- t.cpt +. (cur -. t.u);
  t.paused <- true


let update_t t =
  let time = (times()).tms_utime in
  t.cpt <- t.cpt +. (time -. t.u);
  t.u <- time

let get_t t = t.cpt



let init () =
  let h = Hashtbl.create 8 in
  Hashtbl.add h TSat { u = 0.0; cpt = 0.0; active = false ; paused = true};
  Hashtbl.add h TMatch { u = 0.0; cpt = 0.0; active = false ; paused = true };
  Hashtbl.add h TCC { u = 0.0; cpt = 0.0; active = false ; paused = true };
  Hashtbl.add h TArith { u = 0.0; cpt = 0.0; active = false ; paused = true };
  Hashtbl.add h TArrays { u = 0.0; cpt = 0.0; active = false ; paused = true };
  Hashtbl.add h TSum { u = 0.0; cpt = 0.0; active = false ; paused = true };
  Hashtbl.add h TRecords { u = 0.0; cpt = 0.0; active = false ; paused = true };
  Hashtbl.add h TAc { u = 0.0; cpt = 0.0; active = false ; paused = true };
  h

let reset = 
  Hashtbl.iter (fun _ t -> 
    t.u <- 0.0; 
    t.cpt <- 0.0; 
    t.active <- false;
    t.paused <- true)


let pause h t = pause_t (Hashtbl.find h t)


let pause h t =
  let cur = (times()).tms_utime in
  Hashtbl.iter (fun x it -> 
    if x = t then pause_t it cur
    else if it.active then start_t it cur
  ) h

let update h t = update_t (Hashtbl.find h t)

let pause_all =
  let cur = (times()).tms_utime in
  Hashtbl.iter (fun _ it -> pause_t it cur)

let start h t =
  let cur = (times()).tms_utime in
  Hashtbl.iter (fun x it -> 
    if x = t then start_t it cur
    else if it.active then pause_active_t it cur
  ) h

let pause_and_restart h t f =
  pause h t;
  f ();
  start h t

let get h t = get_t (Hashtbl.find h t)
