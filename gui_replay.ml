open Gui_session


let replay = function
  | Prune id ->
    prune_nodep ~not_register:true (find_by_id id)
  | IncorrectPrune id -> 
    incorrect_prune_nodep ~not_register:true (find_by_id id)
  | Unprune id ->
    unprune_nodep ~not_register:true (find_by_id id)
  | AddInstance of int * string list
  | AddTrigger of int * string list
  | LimitLemma of int * string


let undo_action () =
  match Stack.pop actions with
    | Prune id -> replay (Unprune id)
    | Unprune id -> replay (Prune id)
    | ((AddInstance _ | AddTrigger _ ) as ac) ->
      replay (Prune Hashtbl.find ac resulting_ids)
    | LimitLemma (id, _) -> 
      try 
	Stack.iter (function 
	  | (LimitLemma (id', nb') as ac) when id = id' -> replay ac; raise Exit
	  | _ -> ()) actions;
	replay (LimitLemma (id, "inf"))
      with Exit -> ()
