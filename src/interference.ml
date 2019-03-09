open Format

type arcs = {
  mutable prefs: Register.set;
  mutable intfs: Register.set
}

type igraph = arcs Register.map

type color = Ltltree.operand

type coloring = color Register.map

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

let any_color r c_possible =
  not (Register.S.is_empty c_possible)

let known_pref_color ig colors r c_possible =
  let r_prefs = (Register.M.find r ig).prefs in
  let r_prefs_colored = Register.S.filter (fun r -> Register.M.mem r colors) r_prefs in
  (* let c_prefered = Register.S.map (fun r -> Register.M.find r colors) r_prefs_colored in *)
  not (Register.S.is_empty r_prefs_colored)

let unique_color r c_possible =
  Register.S.cardinal c_possible == 1

let unique_pref_color ig r c_possible =
  Register.S.cardinal c_possible == 1 && Register.S.mem (Register.S.choose c_possible) (Register.M.find r ig).prefs

let filter f todo =
  Register.M.filter f todo

let pick map =
  let r, c_possible = Register.M.choose map in
  Some (r, Ltltree.Reg(Register.S.choose c_possible))

let choose todo ig colors =
  let filtered_unique_pref = filter (unique_pref_color ig) todo in
  if not (Register.M.is_empty filtered_unique_pref) then
    pick filtered_unique_pref
  else
    let filtered_unique = filter unique_color todo in
    if not (Register.M.is_empty filtered_unique) then
      pick filtered_unique
    else
      let filtered_known_pref = filter (known_pref_color ig colors) todo in
      if not (Register.M.is_empty filtered_known_pref) then
        let r, _ = Register.M.choose filtered_known_pref in
        let r_prefs = (Register.M.find r ig).prefs in
        let r_prefs_colored = Register.S.filter (fun r -> Register.M.mem r colors) r_prefs in
        let r_pref_chosen = Register.S.choose r_prefs_colored in
        Some (r, Register.M.find r_pref_chosen colors)
      else
        let filtered_any = filter any_color todo in
        if not (Register.M.is_empty filtered_any) then
          pick filtered_any
        else
          None

let color ig =
  let todo = ref Register.M.empty in
  Register.M.iter (fun r a -> if Register.is_pseudo r then todo := Register.M.add r (Register.S.diff Register.allocatable a.intfs) !todo) ig;
  let colors = ref Register.M.empty in
  Register.S.iter (fun r -> if (Register.M.mem r ig) then colors := Register.M.add r (Ltltree.Reg(r)) !colors) Register.allocatable;
  let num_spilled = ref 0 in
  let rec color_one_pseudo () =
    if Register.M.is_empty !todo then ()
    else (
      match choose !todo ig !colors with
      | None ->
        let r, _ = Register.M.choose !todo in
        todo := Register.M.remove r !todo;
        colors := Register.M.add r (Ltltree.Spilled(!num_spilled)) !colors;
        num_spilled := !num_spilled + 8
      | Some (r, (Reg(c) as color)) ->
        todo := Register.M.remove r !todo;
        let update_intf r_intf =
          let remove_color = function
            | None -> None
            | Some c_possible -> Some (Register.S.remove c c_possible)
          in
          todo := Register.M.update r_intf remove_color !todo
        in
        Register.S.iter update_intf (Register.M.find r ig).intfs;
        colors := Register.M.add r color !colors;
        color_one_pseudo ()
      | _ -> assert false
    )
  in
  color_one_pseudo ();
  Register.S.iter (fun r -> if (Register.M.mem r ig) then colors := Register.M.remove r !colors) Register.allocatable;
  !colors

let print ig =
  Register.M.iter (fun r arcs ->
      Format.printf "%s: prefs=@[%a@] intfs=@[%a@]@." (r :> string)
        Register.print_set arcs.prefs Register.print_set arcs.intfs) ig

let print_color fmt = function
  | Ltltree.Reg hr    -> fprintf fmt "%a" Register.print hr
  | Ltltree.Spilled n -> fprintf fmt "stack %d" n

let print_coloring cm =
  Register.M.iter
    (fun r cr -> printf "%a -> %a@\n" Register.print r print_color cr) cm

let print_file fmt (p: Ertltree.file) =
  Format.fprintf fmt "=== Interference Graph =================================================@\n";
  List.iter (fun (f: Ertltree.deffun) -> print(make (Life.liveness f.fun_body))) p.funs;
  Format.fprintf fmt "=== Coloring =================================================@\n";
  List.iter (fun (f: Ertltree.deffun) -> print_coloring(color (make (Life.liveness f.fun_body)))) p.funs;
