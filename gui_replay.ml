open Gui_session
open Why_annoted
open Why_connected


let replay_prune id env =
  match findbyid id env.ast with
    | AD (ad, _) -> prune ~register:false env ad
    | AF (af, _) -> prune ~register:false env af
    | AT at -> prune ~register:false env at
    | QF aq -> prune ~register:false env aq

let replay_incorrect_prune id env =
  match findbyid id env.ast with
    | AD (ad, _) -> incorrect_prune ~register:false env ad
    | AF (af, _) -> incorrect_prune ~register:false env af
    | AT at -> incorrect_prune ~register:false env at
    | QF aq -> incorrect_prune ~register:false env aq

let replay_unprune id env =
  match findbyid id env.ast with
    | AD (ad, _) -> unprune ~register:false env ad
    | AF (af, _) -> unprune ~register:false env af
    | AT at -> unprune ~register:false env at
    | QF aq -> unprune ~register:false env aq

let replay env = function
  | Prune id -> replay_prune id env
  | IncorrectPrune id -> replay_incorrect_prune id env
  | Unprune id -> replay_unprune id env
  | AddInstance (id, aname, entries) -> assert false
    (* add_instance (findform_byid id env.ast) env entries aname *)
  | AddTrigger (id, trs) -> assert false
  | LimitLemma (id , nbstr) -> assert false


let replay_session env =
  let l = ref [] in
  Stack.iter (fun a -> l := a::!l) env.actions;
  List.iter (replay env) !l

let undo_action env =
  match Stack.pop env.actions with
    | Prune id | IncorrectPrune id -> replay env (Unprune id)
    | Unprune id -> replay env (Prune id)
    | ((AddInstance _ | AddTrigger _ ) as ac) ->
      replay env (Prune (Hashtbl.find resulting_ids ac))
    | LimitLemma (id, _) -> 
      try 
	Stack.iter (function 
	  | (LimitLemma (id', nb') as ac) when id = id' -> 
	      replay env ac; raise Exit
	  | _ -> ()) env.actions;
	replay env (LimitLemma (id, "inf"))
      with Exit -> ()

