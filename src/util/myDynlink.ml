(******************************************************************************)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2015 --- OCamlPro                                   *)
(*     This file is distributed under the terms of the CeCILL-C licence       *)
(******************************************************************************)

(** A wrapper of the Dynlink module: we use Dynlink except when we want to
generate a static (native) binary **)

module DummyDL = struct

  type error = string

  exception Error of error

  let error_message s = s

  let loadfile s = ()

end

include Dynlink
