type arcs = {
  mutable prefs: Register.set;
  mutable intfs: Register.set
}

type igraph = arcs Register.map

let make live_info =
  let graph = ref Register.M.empty in
  let find_arcs a =
    if not (Register.M.mem a !graph) then
      graph := Register.M.add a ({prefs = Register.S.empty; intfs = Register.S.empty}) !graph;
    Register.M.find a !graph
  in
  let add_pref _ (live: Life.live_info) =
    match live.instr with
    | Ertltree.Embinop (Mmov, x, y, _) when x != y ->
      let arcs_x = find_arcs x in
      let arcs_y = find_arcs y in
      arcs_x.prefs <- Register.S.add y arcs_x.prefs;
      arcs_y.prefs <- Register.S.add x arcs_y.prefs
    | _ -> ()
  in
  Hashtbl.iter add_pref live_info;
  let add_label _ (live: Life.live_info) = 
    let add_def r_def = 
      let add_intf r_alive =
        match live.instr with
        | Ertltree.Embinop (Mmov, x, y, _) when x == r_alive && y == r_def -> ()
        | _ ->
          if r_alive != r_def then
            let arcs_def = find_arcs r_def in
            let arcs_alive = find_arcs r_alive in
            arcs_alive.intfs <- Register.S.add r_def arcs_alive.intfs;
            arcs_def.intfs <- Register.S.add r_alive arcs_def.intfs
      in
      Register.S.iter add_intf live.outs
    in
    Register.S.iter add_def live.defs
  in
  Hashtbl.iter add_label live_info;
  !graph

let print ig =
    Register.M.iter (fun r arcs ->
      Format.printf "%s: prefs=@[%a@] intfs=@[%a@]@." (r :> string)
        Register.print_set arcs.prefs Register.print_set arcs.intfs) ig

let print_file fmt (p: Ertltree.file) = 
  Format.fprintf fmt "=== Interference Graph =================================================@\n";
  List.iter (fun (f: Ertltree.deffun) -> print(make (Life.liveness f.fun_body))) p.funs