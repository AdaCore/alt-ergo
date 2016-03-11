(******************************************************************************)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2015 --- OCamlPro                                   *)
(*     This file is distributed under the terms of the CeCILL-C licence       *)
(******************************************************************************)

module Default_Unix = struct

  open Unix

  let cur_time () = (times()).tms_utime

  let set_timeout timelimit =
    if timelimit <> 0. then
      ignore (Unix.setitimer Unix.ITIMER_REAL
		{ Unix.it_value = timelimit; Unix.it_interval = 0. })

  let unset_timeout () =
    ignore (Unix.setitimer Unix.ITIMER_REAL
	      { Unix.it_value = 0.; Unix.it_interval = 0. })

end

include Default_Unix

(*
module JavaScript_Unix = struct

  let cur_time () =
    let today = jsnew Js.date_now () in
    let t = Js.to_float (today##getTime()) in
    t /. 1000.

  let set_timeout _ = ()

  let unset_timeout () = ()

end

include JavaScript_Unix
*)
