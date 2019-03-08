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
  (*
     For every label in l_to_li we pick the live_info
     and for every live_info we add the edges (d, o)
     belonging to li.defs X li.outs, as described in the 8th course
  *)
  let add_pref r_1 r_2 =
      let arcs_1 = find_arcs graph r_1 in
      let arcs_2 = find_arcs graph r_2 in
      arcs_1.prefs <- Register.S.add r_2 arcs_1.prefs;
      arcs_2.prefs <- Register.S.add r_1 arcs_2.prefs
  in
  let add_intf r_1 r_2 =
    let arcs_1 = find_arcs graph r_1 in
    let arcs_2 = find_arcs graph r_2 in
    arcs_2.intfs <- Register.S.add r_1 arcs_2.intfs;
    arcs_1.intfs <- Register.S.add r_2 arcs_1.intfs;
  in
  let add_intfs r_dests r_source =
    Register.S.iter (add_intf r_source) (Register.S.remove r_source r_dests)
  in
  let add_arcs_from_li _ (li: Life.live_info) =
    let r_outs = (
      match li.instr with
      | Ertltree.Embinop (Mmov, r_1, r_2, _) ->
        if r_1 != r_2 then add_pref r_1 r_2;
        Register.S.remove r_2 li.outs
      | _ -> li.outs
    ) in
    Register.S.iter (add_intfs r_outs) li.defs
  in
  Hashtbl.iter add_arcs_from_li l_to_li;

  (*clean edges both in interference and preference*)
  Register.M.iter (fun _ a -> a.prefs <- Register.S.diff a.prefs a.intfs) !graph;
  !graph

let print ig =
  Register.M.iter (fun r arcs ->
      Format.printf "%s: prefs=@[%a@] intfs=@[%a@]@." (r :> string)
        Register.print_set arcs.prefs Register.print_set arcs.intfs) ig

let print_file fmt (p: Ertltree.file) =
  Format.fprintf fmt "=== Interference Graph =================================================@\n";
  List.iter (fun (f: Ertltree.deffun) -> print(make (Life.liveness f.fun_body))) p.funs
