




type action =
  | Prune of int
  | Unprune of int
  | AddInstance of int * string * string list
  | AddTrigger of int * string list
  | LimitLemma of int * string


let actions = Stack.empty


let resulting_ids = Hashtbl.create 17


let save_action ac = Stack.push ac actions
