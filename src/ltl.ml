open Ltltree

let graph = ref Label.M.empty

let lookup colored r =
  if Register.is_hw r then
    Reg r
  else
    Register.M.find r colored

let generate (i:Ltltree.instr) =
  let l = Label.fresh () in
  graph := Label.M.add l i !graph;
  l

let instr colored frame_size = function
  | Ertltree.Egoto (l) ->
    Egoto (l)
  | Ertltree.Ereturn ->
    Ereturn
  | Ertltree.Ealloc_frame l ->
    let l_add = (if frame_size != 0 then
        generate (Emunop((Ops.Maddi (Int32.of_int frame_size), Reg (Register.rsp), l)))
      else l)
    in
    let l_mov = generate (Embinop (Ops.Mmov, Reg (Register.rsp), Reg (Register.rbp), l_add)) in
    Epush(Reg (Register.rbp), l_mov)
  | Ertltree.Edelete_frame l ->
    let l_pop = generate (Epop(Register.rbp, l)) in
    Embinop (Ops.Mmov, Reg (Register.rbp), Reg (Register.rsp), l_pop)
  | Ertltree.Econst (n, r, l) ->
    Econst (n, lookup colored r, l)
  | Ertltree.Eget_param (off, r, l) -> (
      match lookup colored r with
      | Reg r_p -> Eload (r_p, off, Register.rbp, l)
      | Spilled fs ->
        let l_load = generate (Estore(Register.tmp1, Register.rbp, fs, l)) in
        Eload(Register.rbp, off, Register.tmp1, l_load)
    )
  | Ertltree.Embinop (op ,r1, r2, l) -> (
    let r_c1, r_c2 = lookup colored r1, lookup colored r2 in
    match op with
    | Ops.Mmov when r_c1 = r_c2 -> Egoto l
    | Ops.Mmul -> (match r_c2 with
        | Reg r_p2 -> Embinop (op, r_c1, r_c2, l)
        | Spilled fs2 ->
          let l_after = generate (Estore (Register.tmp1, Register.rbp, fs2, l)) in
          let l_mul = generate (Embinop (op, r_c1, Reg Register.tmp1, l_after)) in
          Eload (Register.rbp, fs2, Register.tmp1, l_mul)
      )
    | _ -> (match r_c1, r_c2 with
        | Spilled fs1, Spilled _ ->
          let l_op = generate (Embinop (op, Reg Register.tmp1, r_c2, l)) in
          Eload (Register.rbp, fs1, Register.tmp1, l_op)
        | _ -> Embinop (op, r_c1, r_c2, l)
      )
  )
  | Ertltree.Ecall (id, num_args, l) ->
    Ecall (id, l)
  | Ertltree.Epush_param (r, l) ->
    Epush (lookup colored r, l)
  | Ertltree.Emunop (op , r, l)->
    Emunop (op , lookup colored r, l)
  | Ertltree.Emubranch (b, r, l1, l2) ->
    Emubranch (b, lookup colored r, l1, l2)
  | Ertltree.Embbranch (b, r1, r2, l1, l2) ->
    Embbranch (b, lookup colored r1, lookup colored r2, l1, l2)
  | Ertltree.Eload (r1, n, r2, l) -> (
      match lookup colored r1, lookup colored r2 with
      | Reg r_c1, Reg r_c2 -> Eload (r_c1, n, r_c2, l)
      | Reg r_c1, Spilled fs2 ->
        let l_mov = generate (Estore(Register.tmp1, Register.rbp, fs2, l)) in
        Eload (r_c1, n, Register.tmp1, l_mov)
      | Spilled fs1, Reg r_c2 ->
        let l_load = generate (Eload (Register.tmp1, n, r_c2, l)) in
        Eload(Register.tmp1, fs1, Register.rbp, l_load)
      | Spilled fs1, Spilled fs2 ->
        let l_mov = generate (Estore (Register.tmp2, Register.rbp, fs2, l)) in
        let l_load = generate (Eload (Register.tmp1, n, Register.tmp2, l_mov)) in
        Eload (Register.rbp, fs1, Register.tmp1, l_load)
    )
  | Ertltree.Estore (r1, r2, n, l) -> (
      match lookup colored r1, lookup colored r2 with
      | Reg r_c1, Reg r_c2 -> Estore (r_c1, r_c2, n, l)
      | Reg r_c1, Spilled fs2 ->
        let l_mov = generate (Estore (r_c1, Register.tmp1, n, l)) in
        Eload(Register.rbp, fs2, Register.tmp1, l_mov)
      | Spilled fs1, Reg r_c2 ->
        let l_load = generate (Estore(Register.tmp1, r_c2, n, l)) in
        Eload (Register.rbp, fs1, Register.tmp1, l_load)
      | Spilled fs1, Spilled fs2 ->
        let l_mov = generate (Estore (Register.tmp1, Register.tmp2, n, l)) in
        let l_load = generate (Eload(Register.rbp, fs2, Register.tmp2, l_mov)) in
        Eload(Register.rbp, fs1, Register.tmp1, l_load)
    )

let ertl_to_ltl colored frame_size (l:Label.t) (i:Ertltree.instr) =
  let instr_ltl = instr colored frame_size i in
  graph := Label.M.add l instr_ltl !graph

let deffun (df: Ertltree.deffun) =
  graph := Label.M.empty;
  let live_analysis = Life.liveness df.fun_body in
  let ig = Interference.make live_analysis in
  let colored, frame_size = Interference.color ig in
  Label.M.iter (ertl_to_ltl colored frame_size) df.fun_body;
  {
    fun_name = df.fun_name;
    fun_entry = df.fun_entry;
    fun_body = !graph;
  }

let program (file: Ertltree.file) =
  { funs = List.map deffun file.funs}
