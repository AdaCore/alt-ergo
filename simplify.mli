
open Why_ptree

type decl_list = (int tdecl, int) annoted list
val simplify : decl_list -> decl_list

val split_conjunction_in_hyps : decl_list -> decl_list

(* simplify and split all conjunction-hypothesis *)
val preprocessing : decl_list -> decl_list
