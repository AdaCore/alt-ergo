open Gui_session


let replay = function
  | Prune id ->
    prune_nodep ~not_register:true (findbyid id env.ast)
  | IncorrectPrune id -> 
    incorrect_prune_nodep ~not_register:true (findbyid id env.ast)
  | Unprune id ->
    unprune_nodep ~not_register:true (findbyid id env.ast)
  | AddInstance (id, aname, entries) ->
    add_instance (findform_byid id env.ast) env entries aname
  | AddTrigger (id, trs) -> assert false
  | LimitLemma (id , nbstr) -> assert false


let undo_action () =
  match Stack.pop actions with
    | Prune id -> replay (Unprune id)
    | Unprune id -> replay (Prune id)
    | ((AddInstance _ | AddTrigger _ ) as ac) ->
      replay (Prune (Hashtbl.find ac resulting_ids))
    | LimitLemma (id, _) -> 
      try 
	Stack.iter (function 
	  | (LimitLemma (id', nb') as ac) when id = id' -> replay ac; raise Exit
	  | _ -> ()) actions;
	replay (LimitLemma (id, "inf"))
      with Exit -> ()

