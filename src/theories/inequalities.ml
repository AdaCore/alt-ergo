(******************************************************************************)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2015 --- OCamlPro                                   *)
(*     This file is distributed under the terms of the CeCILL-C licence       *)
(******************************************************************************)

(******************************************************************************)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*   This file is distributed under the terms of the CeCILL-C licence         *)
(******************************************************************************)

open Format

module Z = Numbers.Z
module Q = Numbers.Q

module type EXTENDED_Polynome = sig
  include Polynome.T
  val extract : r -> t option
  val embed : t -> r
end

module type S = sig

  module P : EXTENDED_Polynome
  module MP : Map.S with type key = P.t

  type t = {
      ple0 : P.t;
      is_le : bool;
      dep : (Q.t * P.t * bool) Literal.LT.Map.t;
      expl : Explanation.t;
      age : Z.t;
    }

  module MINEQS : sig
    type mp = (t * Q.t) MP.t
    val empty : mp
    val is_empty : mp -> bool
    val younger : t -> t -> bool
    val insert : t -> mp -> mp
    val ineqs_of : mp -> t list
    val add_to_map : mp -> t list -> mp
    val iter : (P.t -> (t * Q.t) -> unit) -> mp -> unit
    val fold : (P.t -> (t * Q.t) -> 'a -> 'a) -> mp -> 'a -> 'a
  end

  val current_age : unit -> Numbers.Z.t
  val incr_age : unit -> unit

  val create_ineq :
    P.t -> P.t -> bool -> Literal.LT.t -> Explanation.t -> t

  val print_inequation : Format.formatter -> t -> unit

  val fourierMotzkin :
    ('are_eq -> 'acc -> t list -> 'acc) -> 'are_eq -> 'acc ->
    MINEQS.mp -> 'acc

  val fmSimplex :
    ('are_eq -> 'acc -> t list -> 'acc) -> 'are_eq -> 'acc ->
    MINEQS.mp -> 'acc

  val available :
    ('are_eq -> 'acc -> t list -> 'acc) -> 'are_eq -> 'acc ->
    MINEQS.mp -> 'acc

end

module type Container_SIG = sig
  module Make
    (X : Sig.X)
    (Uf : Uf.S with type r = X.r)
    (P : EXTENDED_Polynome with type r = X.r)
    : S with module P = P

end

module Container : Container_SIG = struct
  module Make
    (X : Sig.X)
    (Uf : Uf.S with type r = X.r)
    (P : EXTENDED_Polynome with type r = X.r)
    : S with module P = P = struct

      module P = P
      module MP = Map.Make(P)
      module SP = Set.Make(P)
      module SX = Set.Make(struct type t = X.r let compare = X.hash_cmp end)
      module MX = Map.Make(struct type t = X.r let compare = X.hash_cmp end)
      module MPL = Literal.LT.Map

      type r = P.r
      type uf = Uf.t

      let age_cpt = ref Z.zero

      let current_age () = !age_cpt

      let incr_age () =  age_cpt := Z.add !age_cpt Z.one;

      type t = {
        ple0 : P.t;
        is_le : bool;
        dep : (Q.t * P.t * bool) MPL.t;
        expl : Explanation.t;
        age : Z.t;
      }

      let print_inequation fmt ineq =
        fprintf fmt "%a %s 0 %a" P.print ineq.ple0
          (if ineq.is_le then "<=" else "<") Explanation.print ineq.expl

      let create_ineq p1 p2 is_le a expl =
        let p = P.add p1 (P.mult (P.create [] Q.m_one (P.type_info p1)) p2) in
        { ple0 = p; is_le = is_le; dep = MPL.singleton a (Q.one, p, is_le);
          expl = expl; age = !age_cpt }

      let find_coefficient x ineq = P.find x ineq.ple0

      let split_pos_neg _ ({ple0 = p ; age = age},_) (mx, nb_max) =
        let mx = List.fold_left (fun m (c,x) ->
	  let cmp = Q.sign c in (* equiv. to compare c Q.zero *)
	  if cmp = 0 then m
	  else
	    let (pos, neg) = try MX.find x m with Not_found -> (0,0) in
	    if cmp > 0 then MX.add x (pos+1, neg) m
	    else MX.add x (pos, neg+1) m ) mx (fst (P.to_list p))
        in
        mx, if Z.equal age !age_cpt then nb_max + 1 else nb_max

      module MINEQS = struct

        type mp = (t * Q.t) MP.t

        let empty = MP.empty

        let is_empty mp = MP.is_empty mp

        let younger ineq' ineq =
        (* requires more work in Explanation
           Explanation.younger ineq'.expl ineq.expl ||*)
          Z.compare ineq'.age ineq.age <= 0

        let insert ineq mp =
        (* ineq.ple0  == is ==  p0 + ctt <(=) 0 i.e. p0 <(=) -ctt *)
          let p0, ctt = P.separate_constant ineq.ple0 in
          try
            let ineq', ctt' = MP.find p0 mp in
          (* ineq'.ple0  == is ==  p0 + ctt' <(=) 0 i.e. p0 <(=) -ctt' *)
            let cmp = Q.compare ctt' ctt in
            if cmp = 0 then
              if ineq.is_le = ineq'.is_le then (* equivalent *)
                if younger ineq' ineq then mp
                else MP.add p0 (ineq, ctt) mp
              else
                if ineq.is_le then mp (* ineq' more precise, because it has < *)
                else MP.add p0 (ineq, ctt) mp (*ineq has < -c and ineq' <= -c *)
            else
              if cmp > 0 then (* i.e. ctt' > ctt, i.e. p0 <(=) -ctt' < -ctt *)
                mp (* ineq' is more precise *)
              else (* cmp < 0 i.e. ctt' < ctt, i.e. - ctt' > - ctt >(=) p0 *)
                MP.add p0 (ineq, ctt) mp (* ineq is more precise *)
          with Not_found -> MP.add p0 (ineq, ctt) mp

        let ineqs_of mp = MP.fold (fun _ (ineq, _) acc -> ineq :: acc) mp []

        let add_to_map mp l = List.fold_left (fun mp v -> insert v mp) mp l

        let iter = MP.iter

        let fold = MP.fold

      end

      module Debug = struct

        let list_of_ineqs fmt =
          List.iter (fprintf fmt "%a  " print_inequation)

        let map_of_ineqs fmt =
          MINEQS.iter (fun _ (i , _) -> fprintf fmt "%a  " print_inequation i)

        let cross x cpos cneg others ninqs =
          if Options.debug_fm () then begin
	    fprintf Options.fmt "[fm] We cross on %a@." X.print x;
	    fprintf Options.fmt "with:@. cpos = %a@. cneg = %a@. others = %a@."
	      list_of_ineqs cpos list_of_ineqs cneg map_of_ineqs others;
	    fprintf Options.fmt "result:@.  ninqs = %a@."
	      list_of_ineqs ninqs
          end
      end

      let mult_list c dep =
        if Q.equal c Q.one then dep
        else
          MPL.fold
            (fun a (coef,p,is_le) dep ->
              MPL.add a (Q.mult coef c, p, is_le) dep
            )dep MPL.empty

      let merge_deps d1 d2 =
        MPL.merge
          (fun k op1 op2 ->
            match op1, op2 with
            | None, None -> None
            | Some _, None -> op1
            | None, Some _ -> op2
            | Some(c1,p1, is_le1), Some(c2,p2, is_le2) ->
              assert (P.equal p1 p2 && is_le1 = is_le2);
              Some (Q.add c1 c2, p1, is_le1)
          )d1 d2

      let cross x cpos cneg =
        let rec cross_rec acc l =
          Options.exec_thread_yield ();
          match l with
          | [] -> acc
          | { ple0=p1; is_le=k1; dep=d1; expl=ex1; age=a1 }::l ->
	    let n1 = Q.abs (P.find x p1) in
	    let acc =
	      List.fold_left
	        (fun acc
                  {ple0=p2; is_le=k2; dep=d2; expl=ex2; age=a2} ->
		    Options.exec_thread_yield ();
		    let n2 = Q.abs (P.find x p2) in
		    let p = P.add
		      (P.mult (P.create [] n2 (P.type_info p2)) p1)
		      (P.mult (P.create [] n1 (P.type_info p1)) p2) in
		    let d1 = mult_list n2 d1 in
		    let d2 = mult_list n1 d2 in
		    let ni =
		      { ple0 = p;  is_le = k1&&k2;
                        dep = merge_deps d1 d2;
                        age = Z.max a1 a2;
		        expl = Explanation.union ex1 ex2 }
		    in
		    ni::acc
	        ) acc cpos
	    in
	    cross_rec acc l
        in
        cross_rec [] cneg

      let split x mp =
        let rec split_rec _ (ineq, _) (cp, cn, co) =
          try
	    let a = find_coefficient x ineq in
	    if Q.sign a > 0 then ineq::cp, cn, co
	    else cp, ineq::cn, co
          with Not_found -> cp, cn, MINEQS.insert ineq co
        in
        MINEQS.fold split_rec mp ([], [], MINEQS.empty)

      let choose_var mp =
        let pos_neg, nb_max = MINEQS.fold split_pos_neg mp (MX.empty, 0) in
        if nb_max = 0 then raise Not_found;
        let xopt = MX.fold (fun x (pos, neg) acc ->
          match acc with
	  | None -> Some (x, pos * neg)
	  | Some (y, c') ->
	    let c = pos * neg in
	    if c < c' then Some (x, c) else acc
        ) pos_neg None in
        match xopt with
        | Some (x, _) -> x
        | None -> raise Not_found


      let fourierMotzkin add_ineqs are_eq acc mp =
        let rec fourier acc mp =
          Options.exec_thread_yield ();
          if MINEQS.is_empty mp then acc
          else
	    try
              let x = choose_var mp in
	      let cpos, cneg, others = split x mp in
	      let ninqs = cross x cpos cneg in
	      Debug.cross x cpos cneg others ninqs;
	      let acc = add_ineqs are_eq acc cpos in
	      let acc = add_ineqs are_eq acc cneg in
	      fourier acc (MINEQS.add_to_map others ninqs)
            with Not_found -> add_ineqs are_eq acc (MINEQS.ineqs_of mp)
        in
        fourier acc mp

      let fmSimplex add_ineqs are_eq acc mp =
        let msg =
          "Not implemented in the default version!"^
            "Use the FmSimplex plugin instead" in
        failwith msg

      let available = fourierMotzkin

    end
end

module FM = Container.Make

let current = ref (module Container : Container_SIG)

let initialized = ref false

let set_current mdl = current := mdl

let load_current_inequalities_reasoner () =
  match Options.inequalities_plugin () with
  | "" ->
    if Options.debug_fm () then
      eprintf "[Dynlink] Using the 'FM module' for arithmetic inequalities@."

  | path ->
    if Options.debug_fm () then
      eprintf "[Dynlink] Loading the 'inequalities' reasoner in %s ...@." path;
    try
      Dynlink.loadfile path;
      if Options.debug_fm () then  eprintf "Success !@.@."
    with
    | Dynlink.Error m1 ->
      if Options.debug_fm() then begin
        eprintf
          "[Dynlink] Loading the 'inequalities' reasoner in \"%s\" failed!@."
          path;
        Format.eprintf ">> Failure message: %s@.@." (Dynlink.error_message m1);
      end;
      let prefixed_path = sprintf "%s/%s" Config.pluginsdir path in
      if Options.debug_fm () then
        eprintf
          "[Dynlink] Loading the 'inequalities' reasoner in %s with prefix %s@."
          path Config.pluginsdir;
      try
        Dynlink.loadfile prefixed_path;
        if Options.debug_fm () then  eprintf "Success !@.@."
      with
      | Dynlink.Error m2 ->
        if not (Options.debug_fm()) then begin
          eprintf
            "[Dynlink] Loading the 'inequalities' reasoner in \"%s\" failed!@."
            path;
          Format.eprintf ">> Failure message: %s@.@."
            (Dynlink.error_message m1);
        end;
        eprintf
          "[Dynlink] Trying to load the plugin from \"%s\" failed too!@."
          prefixed_path;
        Format.eprintf ">> Failure message: %s@.@." (Dynlink.error_message m2);
        exit 1

let get_current () =
  if not !initialized then
    begin
      load_current_inequalities_reasoner ();
      initialized := true;
    end;
  !current
