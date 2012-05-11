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

open Why_ptree
open Why_annoted
open Why_connected

open Lexing
open Format
open Options

let inf = Glib.Utf8.from_unichar 8734

let () = 
  try 
    let _ = GMain.init () in
    Options.profiling := true;
    Options.thread_yield := Thread.yield
      
  with Gtk.Error s -> eprintf "%s@." s

(* GTK *)

let window_width = 950
let window_height = 700
let show_discharged = ref false


let w = 
  GWindow.window
    ~title:"AltGr-Ergo"
    ~allow_grow:true
    ~allow_shrink:true
    ~width:window_width
    ~height:window_height ()


let save_session envs =
  let session_cout =
    open_out_gen [Open_creat; Open_wronly; Open_binary] 0o640 !session_file in
  List.iter (fun env -> output_value session_cout env.actions) envs;
  close_out session_cout

let quit envs () =
  save_session envs;
  GMain.quit ()


let pop_error ?(error=false) ~message () =
  let pop_w = GWindow.dialog
    ~title:(if error then "Error" else "Warning")
    ~allow_grow:true
    ~width:400 ()
  in
  let bbox = GPack.button_box `HORIZONTAL ~border_width:5 ~layout:`END
    ~child_height:20 ~child_width:85 ~spacing:10
    ~packing:pop_w#action_area#add () in
  
  let button_ok = GButton.button ~packing:bbox#add () in
  let phbox = GPack.hbox ~packing:button_ok#add () in
  ignore(GMisc.image ~stock:`OK ~packing:phbox#add ());
  ignore(GMisc.label ~text:"OK" ~packing:phbox#add ());
  
  let hbox = GPack.hbox ~border_width:5 ~packing:pop_w#vbox#pack () in
  
  ignore(GMisc.image ~stock:(if error then `DIALOG_ERROR else `DIALOG_WARNING)
	   ~icon_size:`DIALOG ~packing:hbox#pack ());
  ignore(GMisc.label ~text:message
	   ~xalign:0. ~xpad:10 ~packing:hbox#add ());
  ignore(button_ok#connect#clicked ~callback: pop_w#destroy);
  pop_w#show ()



let compare_rows icol_number (model:#GTree.model) row1 row2 =
  let t1 = model#get ~row:row1 ~column:icol_number in
  let t2 = model#get ~row:row2 ~column:icol_number in
  compare t1 t2


let empty_inst_model () = 
  let icols = new GTree.column_list in
  let icol_icon = icols#add GtkStock.conv in
  let icol_desc = icols#add Gobject.Data.string in
  let icol_number = icols#add Gobject.Data.int in
  let icol_limit = icols#add Gobject.Data.string in
  let icol_tag = icols#add Gobject.Data.int in
  let istore = GTree.list_store icols in
  istore#set_sort_func icol_number.GTree.index (compare_rows icol_number);
  istore#set_sort_func icol_desc.GTree.index (compare_rows icol_desc);
  istore#set_sort_column_id icol_number.GTree.index `DESCENDING;
  {
    h = Hashtbl.create 17;
    max = 0;
    icols = icols;
    icol_icon = icol_icon;
    icol_desc = icol_desc;
    icol_number = icol_number;
    icol_limit = icol_limit;
    icol_tag = icol_tag;
    istore = istore;
  }


let empty_timers_model (table:GPack.table) =
  let t =
  {
    timers = Timers.init ();

    label_sat =
      GMisc.label ~text:"SAT" ~justify:`LEFT ~xalign:0.
	~packing:(table#attach ~left:0 ~top:0) ();
    label_match =
      GMisc.label ~text:"Matching" ~justify:`LEFT ~xalign:0.
	~packing:(table#attach ~left:0 ~top:1) ();
    label_cc = 
      GMisc.label ~text:"CC(X)" ~justify:`LEFT ~xalign:0.
	~packing:(table#attach ~left:0 ~top:2) ();
    label_arith = 
      GMisc.label ~text:"Arith" ~justify:`LEFT ~xalign:0.
	~packing:(table#attach ~left:0 ~top:3) ();
    label_arrays = 
      GMisc.label ~text:"Arrays" ~justify:`LEFT~xalign:0. 
	~packing:(table#attach ~left:0 ~top:4) ();
    label_sum = 
      GMisc.label ~text:"Sum" ~justify:`LEFT ~xalign:0.
	~packing:(table#attach ~left:0 ~top:5) ();
    label_records =
      GMisc.label ~text:"Records" ~justify:`LEFT ~xalign:0.
	~packing:(table#attach ~left:0 ~top:6) ();
    label_ac =
      GMisc.label ~text:"AC(X)" ~justify:`LEFT ~xalign:0.
	~packing:(table#attach ~left:0 ~top:7) ();

    tl_sat =
      GMisc.label ~text:"0.000 s" ~justify:`RIGHT 
	~packing:(table#attach ~left:1 ~top:0) ();
    tl_match =
      GMisc.label ~text:"0.000 s" ~justify:`RIGHT 
	~packing:(table#attach ~left:1 ~top:1) ();
    tl_cc = 
      GMisc.label ~text:"0.000 s" ~justify:`RIGHT 
	~packing:(table#attach ~left:1 ~top:2) ();
    tl_arith = 
      GMisc.label ~text:"0.000 s" ~justify:`RIGHT 
	~packing:(table#attach ~left:1 ~top:3) ();
    tl_arrays = 
      GMisc.label ~text:"0.000 s" ~justify:`RIGHT 
	~packing:(table#attach ~left:1 ~top:4) ();
    tl_sum = 
      GMisc.label ~text:"0.000 s" ~justify:`RIGHT 
	~packing:(table#attach ~left:1 ~top:5) ();
    tl_records =
      GMisc.label ~text:"0.000 s" ~justify:`RIGHT 
	~packing:(table#attach ~left:1 ~top:6) ();
    tl_ac =
      GMisc.label ~text:"0.000 s" ~justify:`RIGHT 
	~packing:(table#attach ~left:1 ~top:7) ();

    pr_sat =
      GRange.progress_bar ~packing:(table#attach ~left:2 ~top:0  
				      ~expand:`X ~shrink:`BOTH) ();
    pr_match =
      GRange.progress_bar ~packing:(table#attach ~left:2 ~top:1  
				      ~expand:`X ~shrink:`BOTH) ();
    pr_cc = 
      GRange.progress_bar ~packing:(table#attach ~left:2 ~top:2  
				      ~expand:`X ~shrink:`BOTH) ();
    pr_arith = 
      GRange.progress_bar ~packing:(table#attach ~left:2 ~top:3  
				      ~expand:`X ~shrink:`BOTH) ();
    pr_arrays = 
      GRange.progress_bar ~packing:(table#attach ~left:2 ~top:4  
				      ~expand:`X ~shrink:`BOTH) ();
    pr_sum = 
      GRange.progress_bar ~packing:(table#attach ~left:2 ~top:5  
				      ~expand:`X ~shrink:`BOTH) ();
    pr_records =
      GRange.progress_bar ~packing:(table#attach ~left:2 ~top:6  
				      ~expand:`X ~shrink:`BOTH) ();
    pr_ac =
      GRange.progress_bar ~packing:(table#attach ~left:2 ~top:7  
				      ~expand:`X ~shrink:`BOTH) ();
  } in
  
  t.pr_sat#set_text " 0 %";
  t.pr_match#set_text  " 0 %";
  t.pr_cc#set_text " 0 %";
  t.pr_arith#set_text  " 0 %";
  t.pr_arrays#set_text  " 0 %";
  t.pr_sum#set_text  " 0 %";
  t.pr_records#set_text " 0 %";
  t.pr_ac#set_text  " 0 %";
  t
  

let pump () =
    while Glib.Main.iteration false do () done

let refresh_timers t () =
  let tsat = Timers.get t.timers Timers.TSat in
  let tmatch = Timers.get t.timers Timers.TMatch in
  let tcc = Timers.get t.timers Timers.TCC in
  let tarith = Timers.get t.timers Timers.TArith in
  let tarrays = Timers.get t.timers Timers.TArrays in
  let tsum = Timers.get t.timers Timers.TSum in
  let trecords = Timers.get t.timers Timers.TRecords in
  let tac = Timers.get t.timers Timers.TAc in

  let total = 
    tsat +. tmatch +. tcc +. tarith +. tarrays +. tsum +. trecords +. tac in

  let total = if total = 0. then 1. else total in
  (* eprintf "%f@.%f@.%f@.%f@." *)
  (*   tsat total (tsat /. total) (tsat *. 100. /. total); *)

  t.tl_sat#set_text (sprintf "%3.2f s" tsat);
  t.tl_match#set_text (sprintf "%3.2f s" tmatch);
  t.tl_cc#set_text (sprintf "%3.2f s" tcc);
  t.tl_arith#set_text (sprintf "%3.2f s" tarith);
  t.tl_arrays#set_text (sprintf "%3.2f s" tarrays);
  t.tl_sum#set_text (sprintf "%3.2f s" tsum);
  t.tl_records#set_text (sprintf "%3.2f s" trecords);
  t.tl_ac#set_text (sprintf "%3.2f s" tac);

  t.pr_sat#set_fraction (tsat /. total);
  t.pr_sat#set_text (sprintf "%2.0f %%" (tsat *. 100. /. total));

  t.pr_match#set_fraction (tmatch /. total);
  t.pr_match#set_text (sprintf "%2.0f %%" (tmatch *. 100. /. total));

  t.pr_cc#set_fraction (tcc /. total);
  t.pr_cc#set_text (sprintf "%2.0f %%" (tcc *. 100. /. total));

  t.pr_arith#set_fraction (tarith /. total);
  t.pr_arith#set_text (sprintf "%2.0f %%" (tarith *. 100. /. total));

  t.pr_arrays#set_fraction (tarrays /. total);
  t.pr_arrays#set_text (sprintf "%2.0f %%" (tarrays *. 100. /. total));

  t.pr_sum#set_fraction (tsum /. total);
  t.pr_sum#set_text (sprintf "%2.0f %%" (tsum *. 100. /. total));

  t.pr_records#set_fraction (trecords /. total);
  t.pr_records#set_text (sprintf "%2.0f %%" (trecords *. 100. /. total));

  t.pr_ac#set_fraction (tac /. total);
  t.pr_ac#set_text (sprintf "%2.0f %%" (tac *. 100. /. total));

  true


let reset_timers timers_model =
  Timers.reset timers_model.timers;
  ignore (refresh_timers timers_model ())



let refresh_instances ({istore=istore} as inst_model) () =
  (* eprintf "refresh@."; *)
  Hashtbl.iter (fun id (r, n, name, limit) -> 
    let row, upd_info = 
      match !r with
	| Some row -> row, false
	| None ->
	  let row = istore#append () in
	  r := Some row;
	  row, true in
    let nb = !n in
    (* eprintf "refresh: %s %d@." name nb; *)
    inst_model.max <- max inst_model.max nb;
    if upd_info then begin
      istore#set ~row ~column:inst_model.icol_icon `INFO;
      istore#set ~row ~column:inst_model.icol_desc name;
      let slimit = 
	if !limit >= 0 then string_of_int !limit 
	else "∞" in
      istore#set ~row ~column:inst_model.icol_limit slimit;
    end;
    istore#set ~row ~column:inst_model.icol_number nb;
    istore#set ~row ~column:inst_model.icol_tag id
  ) inst_model.h;
  true
    

let add_inst ({h=h} as inst_model) orig =
  (* eprintf "guisafe:%b@." (GtkThread.gui_safe ()); *)
  let id = Formula.id orig in
  let name = 
    match Formula.view orig with 
      | Formula.Lemma {Formula.name=n} when n <> "" -> n
      | _ -> string_of_int id
  in
  let r, n, limit, to_add =
  try
    let r, n, _, limit = Hashtbl.find h id in
    r, n, limit, false
  with Not_found -> ref None, ref 0, ref (-1), true
  in
  if !limit <> -1 && !limit < !n + 1 then raise Exit;
  incr n;
  if to_add then Hashtbl.add h id (r, n, name, limit);
  inst_model.max <- max inst_model.max !n;
  Thread.yield ()


let reset_inst inst_model =
  Hashtbl.iter (fun _ (_, n, _, _) -> n := 0) inst_model.h;
  ignore (refresh_instances inst_model ())


let empty_sat_inst inst_model =
  inst_model.max <- 0;
  reset_inst inst_model;
  Sat.empty_with_inst (add_inst inst_model)

let update_status image label buttonclean env d s steps =
  let satmode = !smtfile or !smt2file or !satmode in 
  match s with
    | Frontend.Unsat dep ->
	let time = Frontend.Time.get () in
	if not satmode then Loc.report std_formatter d.st_loc;
	if satmode then printf "@{<C.F_Red>unsat@}@."
	else printf "@{<C.F_Green>Valid@} (%2.4f) (%Ld)@." time steps;
	if proof then begin 
	  printf "Proof:\n%a@." Explanation.print_proof dep;
	  show_used_lemmas env dep
	end;
	image#set_stock `YES;
	label#set_text (sprintf "  Valid (%2.2f s)" time);
	buttonclean#misc#show ();
	ignore(buttonclean#connect#clicked 
		 ~callback:(fun () -> prune_unused env))
	  
    | Frontend.Inconsistent ->
	if not satmode then 
	  (Loc.report std_formatter d.st_loc; 
	   fprintf fmt "Inconsistent assumption@.")
	else printf "unsat@.";
	image#set_stock `EXECUTE;
	label#set_text "  Inconsistent assumption"
	  
    | Frontend.Unknown ->
	if not satmode then
	  (Loc.report std_formatter d.st_loc; printf "I don't know.@.")
	else printf "unknown@.";
	image#set_stock `NO;
	label#set_text (sprintf "  I don't know (%2.2f s)" (Frontend.Time.get()))
	  
    | Frontend.Sat  ->
	if not satmode then Loc.report std_formatter d.st_loc;
	if satmode then printf "unknown (sat)@." 
	else printf "I don't know@.";
	image#set_stock `NO;
	label#set_text
	  (sprintf "  I don't know (sat) (%2.2f s)" (Frontend.Time.get()))


exception Abort_thread

let interrupt = ref None

let vt_signal =
  match Sys.os_type with
    | "Win32" -> Sys.sigterm
    | _ -> Sys.sigvtalrm

let force_interrupt old_action_ref n =
  (* This function is called just before the thread's timeslice ends *)
  if Some(Thread.id(Thread.self())) = !interrupt then
    raise Abort_thread;
  match !old_action_ref with
    | Sys.Signal_handle f -> f n
    | _ -> fprintf fmt "Not in threaded mode@."


let rec run buttonrun buttonstop buttonclean inst_model timers_model 
    image label thread env () =
  
  (* Install the signal handler: *)
  let old_action_ref = ref Sys.Signal_ignore in
  let old_action = 
    Sys.signal vt_signal (Sys.Signal_handle (force_interrupt old_action_ref)) in
  old_action_ref := old_action;
  
  image#set_stock `EXECUTE;
  label#set_text "  ...";
  buttonstop#misc#show ();
  buttonrun#misc#hide ();
  buttonclean#misc#hide ();
  clear_used_lemmas_tags env;
    
  let ast = to_ast env.ast in
  if debug then fprintf fmt "AST : \n-----\n%a@." print_typed_decl_list ast;

  let ast_pruned =
    if select > 0 then Pruning.split_and_prune select ast
    else [List.map (fun f -> f,true) ast] in

  (* let chan = Event.new_channel () in *)
  
  (* ignore (Thread.create *)
  (*   (fun () -> *)
  (*      (\* Thread.yield (); *\) *)
  (*      ignore (Event.sync (Event.receive chan)); *)
  (*      if debug then fprintf fmt "Waiting thread : signal recieved@."; *)
  (*      buttonstop#misc#hide (); *)
  (*      buttonrun#misc#show () *)
  (*   ) ()); *)

  (* refresh instances *)
  let to_id = 
    GMain.Timeout.add ~ms:300 ~callback:(refresh_instances inst_model)
  in
  let ti_id = 
    GMain.Timeout.add ~ms:500 ~callback:(refresh_timers timers_model)
  in

  reset_timers timers_model;

   thread := Some (Thread.create
    (fun () ->
       (try
	  (* Thread.yield (); *)
	  if debug then fprintf fmt "Starting alt-ergo thread@.";
	  Frontend.Time.start ();

	  Options.timer_start := Timers.start timers_model.timers;
	  Options.timer_pause := Timers.pause timers_model.timers;

	  List.iter 
	    (fun dcl ->
	       let cnf = Cnf.make dcl in
	       ignore (Queue.fold
			 (Frontend.process_decl 
			    (update_status image label buttonclean env))
			 (empty_sat_inst inst_model, true, Explanation.empty) cnf)
	    ) ast_pruned
	with 
	  | Abort_thread ->
	      Timers.update timers_model.timers;
	      if debug then fprintf fmt "alt-ergo thread terminated@.";
	      image#set_stock `DIALOG_QUESTION;
	      label#set_text "  Process aborted";
	      buttonstop#misc#hide ();
	      buttonrun#misc#show ()
	  |  e -> 
	      Timers.update timers_model.timers;
	      let message = sprintf "Error: %s" (Printexc.to_string e) in
	      if debug then fprintf fmt "alt-ergo thread terminated@.";
	      image#set_stock `DIALOG_ERROR;
	      label#set_text (" "^message);
	      buttonstop#misc#hide ();
	      buttonrun#misc#show ();
	      fprintf fmt "%s@." message;
	      pop_error ~error:true ~message ()
       );
       if debug then fprintf fmt "Send done signal to waiting thread@.";
       buttonstop#misc#hide ();
       buttonrun#misc#show ();
       (* Event.sync (Event.send chan true) *)
       Thread.delay 0.001;
       GMain.Timeout.remove to_id;
       GMain.Timeout.remove ti_id;
       ignore (refresh_instances inst_model ());
       ignore (refresh_timers timers_model ())
    ) ());

  Thread.yield ()
  (* ignore (Thread.create (fun () ->  *)
  (* match !thread with Some s -> Thread.join s | _ -> assert false) ()) *)


let rec kill_thread buttonrun buttonstop image label thread () =
  match !thread with 
    | Some r -> 
	interrupt :=  Some (Thread.id r);
	Thread.join r
    | _ -> 
	interrupt := None

let remove_context env () =
  List.iter
    (fun (td, _) ->
       match td.c with
	 | APredicate_def (_, _, _, _) ->
	     toggle_prune env td
	 | AAxiom (_, s, _) 
	     when String.length s = 0 || (s.[0] <> '_'  && s.[0] <> '@') ->
	     toggle_prune env td
	 | _ -> ()
    ) env.ast


let toggle_ctrl env key =
  if GdkEvent.Key.hardware_keycode key = 37 then
    (env.ctrl <- not env.ctrl; true)
  else false


let empty_error_model () = 
  let rcols = new GTree.column_list in
  let rcol_icon = rcols#add GtkStock.conv in
  let rcol_desc = rcols#add Gobject.Data.string in
  let rcol_line = rcols#add Gobject.Data.int in
  let rcol_type = rcols#add Gobject.Data.int in
  let rcol_color = rcols#add Gobject.Data.string in
  {
    some = false;
    rcols = rcols;
    rcol_icon = rcol_icon;
    rcol_desc = rcol_desc;
    rcol_line = rcol_line;
    rcol_type = rcol_type;
    rcol_color = rcol_color;
    rstore = GTree.list_store rcols;
  }


let goto_error (view:GTree.view) error_model buffer 
    (sv:GSourceView2.source_view)  path column =
  let model = view#model in
  let row = model#get_iter path in
  let line = model#get ~row ~column:error_model.rcol_line in
  let iter_line = buffer#get_iter (`LINE (line-1)) in
  let iter_endline = iter_line#forward_line#backward_char in
  buffer#select_range iter_endline iter_line;
  ignore(sv#scroll_to_iter  ~use_align:true ~yalign:0.1 iter_line)
  

let create_error_view error_model buffer sv ~packing () =
  let view = GTree.view ~model:error_model.rstore ~packing () in

  let renderer = GTree.cell_renderer_pixbuf [] in
  let col = GTree.view_column ~title:""  
    ~renderer:(renderer, ["stock_id", error_model.rcol_icon]) () in
  ignore (view#append_column col);
  col#set_sort_column_id error_model.rcol_icon.GTree.index;

  let renderer = GTree.cell_renderer_text [] in
  let col = GTree.view_column ~title:"Line"  
    ~renderer:(renderer, ["text", error_model.rcol_line]) () in
  ignore (view#append_column col);
  col#set_resizable true;
  col#set_sort_column_id error_model.rcol_line.GTree.index;

  let renderer = GTree.cell_renderer_text [] in
  let col = GTree.view_column ~title:"Description"  
    ~renderer:(renderer, ["text", error_model.rcol_desc]) () in
  ignore (view#append_column col);
  col#set_resizable true;
  col#set_sort_column_id error_model.rcol_desc.GTree.index;

  ignore(view#connect#row_activated 
	   ~callback:(goto_error view error_model buffer sv));
  view



let goto_lemma (view:GTree.view) inst_model buffer 
    (sv:GSourceView2.source_view) env path column =
  let model = view#model in
  let row = model#get_iter path in
  let id = model#get ~row ~column:inst_model.icol_tag in
  try
    let line, t = find_line id env.ast in
    let iter_line = buffer#get_iter (`LINE (line-1)) in
    let prev_line = buffer#get_iter (`LINE (line-2)) in
    buffer#place_cursor ~where:iter_line;
    ignore(sv#scroll_to_iter ~use_align:true ~yalign:0.1 prev_line);
    env.last_tag#set_properties 
      [`BACKGROUND_SET false; `UNDERLINE_SET false];
    t#set_property (`BACKGROUND "light blue");                         
    env.last_tag <- t;
  with Not_found -> ()


let colormap = Gdk.Color.get_system_colormap ()

let set_color_inst inst_model renderer (istore:GTree.model) row =
  let id = istore#get ~row ~column:inst_model.icol_tag in
  let _, nb_inst, _, limit = Hashtbl.find inst_model.h id in
  (* let nb_inst = istore#get ~row ~column:inst_model.icol_number in *)
  (* let limit = istore#get ~row ~column:inst_model.icol_limit in *)
  let nb_inst = !nb_inst in 
  let limit = !limit in
  if nb_inst = limit then
    renderer#set_properties [`FOREGROUND "blue"]
  else if inst_model.max <> 0 then
    let perc = (nb_inst * 65535) / inst_model.max in
    let red_n =
      Gdk.Color.alloc colormap (`RGB (perc, 0, 0)) in
    renderer#set_properties [`FOREGROUND_GDK red_n]
  else 
    renderer#set_properties [`FOREGROUND_SET false];
  Thread.yield ()
  

let create_inst_view inst_model env buffer sv ~packing () =
  let view = GTree.view ~model:inst_model.istore ~packing () in

  let renderer = GTree.cell_renderer_pixbuf [] in
  let col = GTree.view_column ~title:""  
    ~renderer:(renderer, ["stock_id", inst_model.icol_icon]) () in
  ignore (view#append_column col);
  col#set_sort_column_id inst_model.icol_icon.GTree.index;

  let renderer = GTree.cell_renderer_text [] in
  let col = GTree.view_column ~title:"#"  
    ~renderer:(renderer, ["text", inst_model.icol_number]) () in
  ignore (view#append_column col);
  col#set_cell_data_func renderer
    (set_color_inst inst_model renderer);
  col#set_resizable true;
  col#set_sort_column_id inst_model.icol_number.GTree.index;

  let renderer = GTree.cell_renderer_text [`EDITABLE true] in
  ignore (renderer#connect#edited (fun path s ->
    let row = inst_model.istore#get_iter path in
    let id = inst_model.istore#get ~row ~column:inst_model.icol_tag in
    let _,_,_,l = Hashtbl.find inst_model.h id in
    try
      let limit = int_of_string s in
      if limit >= 0 then
	begin
	  l := limit;
	  inst_model.istore#set ~row ~column:inst_model.icol_limit 
	    (string_of_int limit)
	end
      else 
	begin
	  l := -1;
	  inst_model.istore#set ~row ~column:inst_model.icol_limit inf
	end
    with Failure _ -> 
      l := -1;
      inst_model.istore#set ~row ~column:inst_model.icol_limit inf
  ));
  let col = GTree.view_column ~title:"limit"  
    ~renderer:(renderer, ["text", inst_model.icol_limit]) () in
  ignore (view#append_column col);
  col#set_resizable true;
  col#set_sort_column_id inst_model.icol_limit.GTree.index;

  let renderer = GTree.cell_renderer_text [] in
  let col = GTree.view_column ~title:"Lemma"  
    ~renderer:(renderer, ["text", inst_model.icol_desc]) () in
  ignore (view#append_column col);
  col#set_cell_data_func renderer
    (set_color_inst inst_model renderer);
  col#set_resizable true;
  col#set_sort_column_id inst_model.icol_desc.GTree.index;


  ignore(view#connect#row_activated 
	   ~callback:(goto_lemma view inst_model buffer sv env));  
  view


let _ =

  let lmanager = GSourceView2.source_language_manager ~default:true in
  let source_language = lmanager#language "alt-ergo" in

  let smanager = GSourceView2.source_style_scheme_manager ~default:true in
  let scheme = smanager#style_scheme "tango" in

  let lb = from_channel cin in
  let typed_ast, _ = 
    try Frontend.open_file !file lb
    with
      | Why_lexer.Lexical_error s -> 
	  Loc.report err_formatter (lexeme_start_p lb, lexeme_end_p lb);
	  printf "lexical error: %s\n@." s;
	  exit 1
      | Parsing.Parse_error ->
	  let  loc = (lexeme_start_p lb, lexeme_end_p lb) in
	  Loc.report err_formatter loc;
          printf "syntax error\n@.";
	exit 1
      | Common.Error(e,l) -> 
	  Loc.report err_formatter l; 
	  printf "typing error: %a\n@." Common.report e;
	  exit 1
  in


  let notebook = 
    GPack.notebook ~border_width:0 ~tab_pos:`BOTTOM
      ~show_border:false 
      ~enable_popup:true 
      ~scrollable:true
      ~packing:w#add () in


  let session_cin =
    try Some (open_in_bin !session_file)
    with Sys_error _ -> None in

  let envs = 
   List.fold_left
    (fun acc l ->
       
       let buf1 = match source_language with 
	 | Some language -> GSourceView2.source_buffer ~language
	     ~highlight_syntax:true ~highlight_matching_brackets:true ()
	 | None -> GSourceView2.source_buffer () in

       let buf2 = match source_language with 
	 | Some language -> GSourceView2.source_buffer ~language
	     ~highlight_syntax:true ~highlight_matching_brackets:true ()
	 | None -> GSourceView2.source_buffer () in

       buf1#set_style_scheme scheme;
       buf2#set_style_scheme scheme;

       let annoted_ast = annot buf1 l in
       if debug then fprintf fmt "Computing dependencies ... ";
       let dep = make_dep annoted_ast in
       if debug then fprintf fmt "Done@.";

       
       let text = List.fold_left
	 (fun _ (td,_) ->
	    match td.c with
	      | AGoal (_, s, _) -> "goal "^s
	      | _ -> "Empty"
	 ) "" annoted_ast in

       let label = GMisc.label ~text () in
       let append g = 
	 ignore(notebook#append_page ~tab_label:label#coerce g); () in
       
       let eventBox = GBin.event_box ~border_width:0 ~packing:append () in
       
       
       let vbox = GPack.vbox 
	 ~homogeneous:false ~border_width:0 ~packing:eventBox#add () in

       let rbox = GPack.vbox ~border_width:0 ~packing:vbox#add () in


       let toolbar = GButton.toolbar ~tooltips:true ~packing:rbox#pack () in
       toolbar#set_icon_size `DIALOG;
       
       let hb = GPack.paned `HORIZONTAL 
	 ~border_width:3 ~packing:rbox#add () in

       let vb1 = GPack.paned `VERTICAL 
	 ~border_width:3 ~packing:(hb#pack1 ~shrink:true ~resize:true) () in
       let vb2 = GPack.paned `VERTICAL 
	 ~border_width:3 ~packing:(hb#pack2 ~shrink:true ~resize:true) () in

       let fr1 = GBin.frame ~shadow_type:`ETCHED_OUT
	 ~width:(60 * window_width / 100)
	 ~height:(80 * window_height / 100)
	 ~packing:(vb1#pack1 ~shrink:true ~resize:true) () in

       let fr2 = GBin.frame ~shadow_type:`ETCHED_OUT
	 ~height:(35 * window_height / 100)
	 ~packing:(vb2#pack1 ~shrink:true ~resize:true) () in

       let fr3 = GBin.frame ~shadow_type:`ETCHED_OUT ~show:false
	 ~packing:(vb1#pack2 ~shrink:true ~resize:true) () in

       let binfo = GPack.vbox ~border_width:0 
	 ~packing:(vb2#pack2 ~shrink:true ~resize:true) () in

       let fr4 = GBin.frame ~shadow_type:`ETCHED_OUT
	 ~packing:binfo#add () in

       let fr5 = GBin.frame ~shadow_type:`NONE
	 ~packing:binfo#pack () in

       let table_timers = GPack.table ~columns:3 ~rows:8
	 ~row_spacings:1 ~col_spacings:8 ~border_width:4
	 ~packing:fr5#add () in


       let st = GMisc.statusbar ~has_resize_grip:false ~border_width:0 
	 ~packing:vbox#pack () in  
       let st_ctx = st#new_context ~name:"Type" in

       let error_model = empty_error_model () in
       let inst_model = empty_inst_model () in
       let timers_model = empty_timers_model table_timers in

       
       let actions = Gui_session.read_actions session_cin in


       let env = create_env buf1 buf2 error_model st_ctx annoted_ast dep 
	 actions in
       connect env;

       Gui_replay.replay_session env;

       ignore (toolbar#insert_toggle_button
	 ~text:" Remove context"
	 ~icon:(GMisc.image ~stock:`CUT ~icon_size:`LARGE_TOOLBAR ())#coerce
	 ~callback:(remove_context env) ());

       let sw1 = GBin.scrolled_window
	    ~vpolicy:`AUTOMATIC 
	    ~hpolicy:`AUTOMATIC
	    ~packing:fr1#add () 
       in
       let tv1 = GSourceView2.source_view ~source_buffer:buf1 ~packing:(sw1#add)
	 ~show_line_numbers:true ~wrap_mode:`NONE 
	 ~highlight_current_line:true ()
       in
       let _ = tv1#misc#modify_font monospace_font in
       let _ = tv1#set_editable false in

       let sw2 = GBin.scrolled_window
	    ~vpolicy:`AUTOMATIC 
	    ~hpolicy:`AUTOMATIC
	    ~packing:fr2#add () 
       in
       let tv2 = GSourceView2.source_view ~source_buffer:buf2 ~packing:(sw2#add)
	 ~show_line_numbers:false ~wrap_mode:`NONE 
	 ~highlight_current_line:true ()
       in
       let _ = tv2#misc#modify_font monospace_font in
       let _ = tv2#set_editable false in

       let buttonrun = toolbar#insert_button
	 ~text:" Run Alt-Ergo"
	 ~icon:(GMisc.image ~stock:`EXECUTE  ~icon_size:`LARGE_TOOLBAR()
	 )#coerce () in

       let buttonstop = toolbar#insert_button
	 ~text:" Abort"
	 ~icon:(GMisc.image ~stock:`STOP  ~icon_size:`LARGE_TOOLBAR()
	 )#coerce () in
	buttonstop#misc#hide ();

       toolbar#insert_space ();

       let resultbox = GPack.hbox () in
       let result_image = GMisc.image ~icon_size:`LARGE_TOOLBAR
	 ~stock:`DIALOG_QUESTION ~packing:resultbox#add () in
       let result_label = GMisc.label
	 ~text:" " ~packing:resultbox#add () in
       
       ignore(toolbar#insert_widget resultbox#coerce);
       
       let buttonclean = toolbar#insert_button
	 ~text:" Clean unused"
	 ~icon:(GMisc.image ~stock:`CLEAR  ~icon_size:`LARGE_TOOLBAR()
	 )#coerce () in
	buttonclean#misc#hide ();


       let sw3 = GBin.scrolled_window
	    ~vpolicy:`AUTOMATIC 
	    ~hpolicy:`AUTOMATIC
	    ~packing:fr3#add () 
       in
       ignore(create_error_view error_model env.buffer tv1 
	 ~packing:sw3#add ());

       add_to_buffer error_model env.buffer env.ast;

       if error_model.some then fr3#misc#show ();

       let sw4 = GBin.scrolled_window
	    ~vpolicy:`AUTOMATIC 
	    ~hpolicy:`AUTOMATIC
	    ~packing:fr4#add () 
       in

       ignore(create_inst_view inst_model env env.buffer tv1 
		~packing:sw4#add ());



       let thread = ref None in
       
       ignore(buttonrun#connect#clicked 
	 ~callback:(run buttonrun buttonstop buttonclean inst_model timers_model
		      result_image result_label thread env));

       ignore(buttonstop#connect#clicked 
	 ~callback:(kill_thread buttonrun buttonstop 
		      result_image result_label thread));

       ignore(eventBox#event#connect#key_press
		~callback:(toggle_ctrl env));

       ignore(eventBox#event#connect#key_release
		~callback:(toggle_ctrl env));
       
       env::acc

    ) [] typed_ast in

  begin
    match session_cin with 
      | Some c -> close_in c
      | None -> ()
  end;

  let envs = List.rev envs in

  ignore(w#connect#destroy ~callback:(quit envs));
  w#show ();

  (* Thread.join(GtkThread.start ()); *)
  GtkThread.main ();

