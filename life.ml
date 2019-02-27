type live_info = {
          instr: Ertltree.instr;
          succ: Label.t list;    (* successeurs *)
  mutable pred: Label.set;       (* prédécesseurs *)
          defs: Register.set;    (* définitions *)
          uses: Register.set;    (* utilisations *)
  mutable  ins: Register.set;    (* variables vivantes en entrée *)
  mutable outs: Register.set;    (* variables vivantes en sortie *)
}

let label_live = Hashtbl.create 255

let add_live_info lab instr =
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
  Hashtbl.add label_live lab info

let set_pred_in_succs l_pred inf_pred = 
  let add_pred l_succ =
    let inf_succ = Hashtbl.find label_live l_succ in
    inf_succ.pred <- Label.S.add l_pred inf_succ.pred
  in
  List.iter add_pred inf_pred.succ

let kildall = 
  let ws = ref Label.S.empty in
  ws := Hashtbl.fold (fun l _ acc -> Label.S.add l acc) label_live !ws;
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
  Label.M.iter add_live_info g;
  Hashtbl.iter set_pred_in_succs label_live;
  kildall;
  label_live

let print_set = Register.print_set

let print_live_info fmt li =
  Format.fprintf fmt "d={%a}@ u={%a}@ i={%a}@ o={%a}"
    print_set li.defs print_set li.uses print_set li.ins print_set li.outs