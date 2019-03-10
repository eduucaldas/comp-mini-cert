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

(* Naming refacto:
   c_possible is actually a register
*)
let any_color r c_possible =
  not (Register.S.is_empty c_possible)

let unique_color r c_possible =
  Register.S.cardinal c_possible == 1

let unique_pref_color ig r c_possible =
  Register.S.cardinal c_possible == 1 && Register.S.mem (Register.S.choose c_possible) (Register.M.find r ig).prefs

let pick_r_w_c criteria (r_to_c_possible: Register.S.t Register.map) =
  match Register.M.choose_opt (
    Register.M.filter criteria r_to_c_possible
  ) with
  | None -> None
  | Some (r, r_c) -> Some (r, Ltltree.Reg (Register.S.choose r_c))

let is_some a =
  match a with
  | None -> false
  | _ -> true

(* Refacto needed *)
let pick_r_w_c_pref_known (colored: coloring) ig (r_to_c_possible: Register.S.t Register.map) =
  let pick_c_pref_known_opt r _ =
    let r_prefs = (Register.M.find r ig).prefs in
    let r_intfs = (Register.M.find r ig).intfs in
    let r_prefs_to_known_colors = Register.M.filter (fun r c -> (Register.S.mem r r_prefs) && (match c with Ltltree.Reg rc -> not (Register.S.mem rc r_intfs) | _ -> assert false)) colored in
    match (Register.M.choose_opt r_prefs_to_known_colors) with
    | None -> None
    | Some (_, c) -> Some c
  in
  let r_w_c_opt = Register.M.choose_opt (
    Register.M.filter
      (fun _ c -> (is_some c))
      (Register.M.mapi
         pick_c_pref_known_opt
         r_to_c_possible
      )
  ) in
  match r_w_c_opt with
  | None -> None
  | Some (r, Some c) -> Some (r, c)
  | Some (r, None) -> assert false

let choose todo ig (colored: coloring) =
  let r_w_c_unique_pref = pick_r_w_c (unique_pref_color ig) todo in
  if (is_some r_w_c_unique_pref) then r_w_c_unique_pref
  else
    let r_w_c_unique = pick_r_w_c unique_color todo in
    if (is_some r_w_c_unique) then r_w_c_unique_pref
    else
      let r_w_c_pref_known = pick_r_w_c_pref_known colored ig todo in
      if (is_some r_w_c_pref_known) then r_w_c_pref_known
      else
        let r_w_c_any = pick_r_w_c any_color todo in
        if (is_some r_w_c_any) then r_w_c_any
        else
          None

(* Refacto needed *)
let color ig =
  let todo: Register.S.t Register.map ref = ref Register.M.empty in
  Register.M.iter (fun r a -> if Register.is_pseudo r then todo := Register.M.add r (Register.S.diff Register.allocatable a.intfs) !todo) ig;
  let colored: coloring ref = ref Register.M.empty in
  let spilled: coloring ref = ref Register.M.empty in
  Register.S.iter (fun r -> if (Register.M.mem r ig) then colored := Register.M.add r (Ltltree.Reg(r)) !colored) Register.allocatable;
  let size_spilled = ref 0 in
  while not (Register.M.is_empty !todo) do
    match choose !todo ig !colored with
    | None ->
      let r, _ = Register.M.choose !todo in
      todo := Register.M.remove r !todo;
      size_spilled := !size_spilled - 8;
      spilled := Register.M.add r (Ltltree.Spilled(!size_spilled)) !spilled;
    | Some (r, (Reg(r_c) as c)) ->
      todo := Register.M.remove r !todo;
      let update_intf r_intf =
        let remove_color = function
          | None -> None
          | Some c_possible -> Some (Register.S.remove r_c c_possible)
        in
        todo := Register.M.update r_intf remove_color !todo
      in
      Register.S.iter update_intf (Register.M.find r ig).intfs;
      colored := Register.M.add r c !colored;
    | _ -> assert false
  done;
  Register.S.iter (fun r -> if (Register.M.mem r ig) then colored := Register.M.remove r !colored) Register.allocatable;
  Register.M.iter (fun r c -> colored := Register.M.add r c !colored) !spilled;
  (!colored, !size_spilled)

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
  List.iter (fun (f: Ertltree.deffun) -> print_coloring(fst (color (make (Life.liveness f.fun_body))))) p.funs;
