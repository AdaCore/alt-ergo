

type action =
  | Prune of int
  | Unprune of int
  | AddInstance of int * string list
  | AddTrigger of int * string list
  | LimitLemma of int * string


