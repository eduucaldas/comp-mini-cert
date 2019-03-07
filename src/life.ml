open Format
open Ertltree

(* li abreviates live_info *)
type live_info = {
          instr: Ertltree.instr;
          succ: Label.t list;    (* successeurs *)
  mutable pred: Label.set;       (* prédécesseurs *)
          defs: Register.set;    (* définitions *)
          uses: Register.set;    (* utilisations *)
  mutable  ins: Register.set;    (* variables vivantes en entrée *)
  mutable outs: Register.set;    (* variables vivantes en sortie *)
}

let add_li l_to_li l instr =
  let succ = Ertltree.succ instr in
  let defs, uses = Ertltree.def_use instr in
  let li = {
    instr = instr;
    succ = succ;
    pred = Label.S.empty;
    defs = Register.set_of_list defs;
    uses = Register.set_of_list uses;
    ins = Register.S.empty;
    outs = Register.S.empty;
  }
  in
  Hashtbl.add l_to_li l li

let set_pred_in_succs l_to_li l_pred li_pred =
  let add_pred l_succ =
    let li_succ = Hashtbl.find l_to_li l_succ in
    li_succ.pred <- Label.S.add l_pred li_succ.pred
  in
  List.iter add_pred li_pred.succ

let kildall l_to_li =
  let ws = ref Label.S.empty in
  Hashtbl.iter (fun l _ -> (ws := Label.S.add l !ws)) l_to_li;
  while not (Label.S.is_empty !ws) do
    let l = Label.S.choose !ws in
    ws := Label.S.remove l !ws;
    let li = Hashtbl.find l_to_li l in
    let in_old = li.ins in
    let get_in_from_label l =
      (Hashtbl.find l_to_li l).ins
    in
    li.outs <- List.fold_left (fun acc l -> Register.S.union (get_in_from_label l) acc)
      Register.S.empty li.succ;
    li.ins <- Register.S.union li.uses (Register.S.diff li.outs li.defs);
    if not (Register.S.equal li.ins in_old) then
      ws := Label.S.fold (fun l acc -> Label.S.add l acc) li.pred !ws
  done

let liveness g =
  let l_to_li = Hashtbl.create 255 in
  Label.M.iter (add_li l_to_li) g;
  Hashtbl.iter (set_pred_in_succs l_to_li) l_to_li;
  kildall l_to_li;
  l_to_li

let print_set = Register.print_set

let print_li fmt li =
  Format.fprintf fmt "d={%a}@ u={%a}@ i={%a}@ o={%a}@\n"
    print_set li.defs print_set li.uses print_set li.ins print_set li.outs

let print_graph_with_life fmt body entry =
  let l_to_li = liveness body in
Ertltree.visit (fun l i -> fprintf fmt "%a: %a " Label.print l print_instr i; print_li fmt (Hashtbl.find l_to_li l)) body entry

let print_with_liveness fmt p =
  fprintf fmt "=== ERTL + Liveness =======================================@\n";
  List.iter ((Ertltree.print_w_header print_graph_with_life) fmt) p.funs
