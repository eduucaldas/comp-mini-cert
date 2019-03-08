type arcs = {
  mutable prefs: Register.set;
  mutable intfs: Register.set
}

type igraph = arcs Register.map

let find_arcs g r =
  match Register.M.find_opt r !g with
  | Some a -> a
  | None ->
    let arc_new = {prefs = Register.S.empty; intfs = Register.S.empty} in
    g := Register.M.add r arc_new !g;
    arc_new

let make l_to_li =
  let graph = ref Register.M.empty in

  let add_pref _ (li: Life.live_info) =
    match li.instr with
    | Ertltree.Embinop (Mmov, r_1, r_2, _) when r_1 != r_2 ->
      let arcs_1 = find_arcs graph r_1 in
      let arcs_2 = find_arcs graph r_2 in
      arcs_1.prefs <- Register.S.add r_2 arcs_1.prefs;
      arcs_2.prefs <- Register.S.add r_1 arcs_2.prefs
    | _ -> ()
  in
  Hashtbl.iter add_pref l_to_li;

  let add_label _ (li: Life.live_info) =
    let add_def r_def =
      let add_intf r_alive =
        match li.instr with
        | Ertltree.Embinop (Mmov, r_1, r_2, _) when r_1 == r_alive && r_2 == r_def -> ()
        | _ ->
          if r_alive != r_def then
            let arcs_def = find_arcs graph r_def in
            let arcs_alive = find_arcs graph r_alive in
            arcs_alive.intfs <- Register.S.add r_def arcs_alive.intfs;
            arcs_def.intfs <- Register.S.add r_alive arcs_def.intfs;
            if Register.S.mem r_alive arcs_def.prefs then
              arcs_alive.prefs <- Register.S.remove r_def arcs_alive.prefs;
              arcs_def.prefs <- Register.S.remove r_alive arcs_def.prefs
      in
      Register.S.iter add_intf li.outs
    in
    Register.S.iter add_def li.defs
  in
  Hashtbl.iter add_label l_to_li;
  !graph

let print ig =
    Register.M.iter (fun r arcs ->
      Format.printf "%s: prefs=@[%a@] intfs=@[%a@]@." (r :> string)
        Register.print_set arcs.prefs Register.print_set arcs.intfs) ig

let print_file fmt (p: Ertltree.file) =
  Format.fprintf fmt "=== Interference Graph =================================================@\n";
  List.iter (fun (f: Ertltree.deffun) -> print(make (Life.liveness f.fun_body))) p.funs
