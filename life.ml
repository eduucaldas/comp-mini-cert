open Format
open Ertltree

type live_info = {
          instr: Ertltree.instr;
          succ: Label.t list;    (* successeurs *)
  mutable pred: Label.set;       (* prédécesseurs *)
          defs: Register.set;    (* définitions *)
          uses: Register.set;    (* utilisations *)
  mutable  ins: Register.set;    (* variables vivantes en entrée *)
  mutable outs: Register.set;    (* variables vivantes en sortie *)
}

let add_live_info label_live l instr =
  let succ = Ertltree.succ instr in
  let defs, uses = Ertltree.def_use instr in
  let info = {
    instr = instr;
    succ = succ;
    pred = Label.S.empty;
    defs = Register.set_of_list defs;
    uses = Register.set_of_list uses;
    ins = Register.S.empty;
    outs = Register.S.empty;
  }
  in
  Hashtbl.add label_live l info

let set_pred_in_succs label_live l_pred inf_pred =
  let add_pred l_succ =
    let inf_succ = Hashtbl.find label_live l_succ in
    inf_succ.pred <- Label.S.add l_pred inf_succ.pred
  in
  List.iter add_pred inf_pred.succ

let kildall label_live =
  let ws = ref Label.S.empty in
  Hashtbl.iter (fun l _ -> (ws := Label.S.add l !ws)) label_live;
  while not (Label.S.is_empty !ws) do
    let l = Label.S.choose !ws in
    ws := Label.S.remove l !ws;
    let inf = Hashtbl.find label_live l in
    let old_in = inf.ins in
    let get_in_from_label l =
      (Hashtbl.find label_live l).ins
    in
    inf.outs <- List.fold_left (fun acc l -> Register.S.union (get_in_from_label l) acc)
      Register.S.empty inf.succ;
    inf.ins <- Register.S.union inf.uses (Register.S.diff inf.outs inf.defs);
    if not (Register.S.equal inf.ins old_in) then
      ws := Label.S.fold (fun l acc -> Label.S.add l acc) inf.pred !ws
  done

let liveness g =
  let label_live = Hashtbl.create 255 in
  Label.M.iter (add_live_info label_live) g;
  Hashtbl.iter (set_pred_in_succs label_live) label_live;
  kildall label_live;
  label_live

let print_set = Register.print_set

let print_live_info fmt li =
  Format.fprintf fmt "d={%a}@ u={%a}@ i={%a}@ o={%a}@\n"
    print_set li.defs print_set li.uses print_set li.ins print_set li.outs

let print_graph_with_life fmt label_live =
Ertltree.visit (fun l i -> fprintf fmt "%a: %a " Label.print l print_instr i; print_live_info fmt (Hashtbl.find label_live l))

let print_deffun_with_liveness fmt f =
  fprintf fmt "%s(%d)@\n" f.fun_name f.fun_formals;
  fprintf fmt "  @[";
  fprintf fmt "entry : %a@\n" Label.print f.fun_entry;
  fprintf fmt "locals: @[%a@]@\n" Register.print_set f.fun_locals;
  let label_live = liveness f.fun_body in
  print_graph_with_life fmt label_live f.fun_body f.fun_entry;
  fprintf fmt "@]@."


let print_with_liveness fmt p =
  fprintf fmt "=== ERTL + Liveness =================================================@\n";
  List.iter (print_deffun_with_liveness fmt) p.funs
