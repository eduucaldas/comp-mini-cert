open Ertltree

let graph = ref Label.M.empty

let generate (i:Ertltree.instr) =
  let l = Label.fresh () in
  graph := Label.M.add l i !graph;
  l

let instr = function
  | Rtltree.Econst (n, r, l) ->
      Ertltree.Econst (n, r, l)
  | Rtltree.Eload (r1, n, r2, l) ->
      Ertltree.Eload (r1, n, r2, l)
  | Rtltree.Estore (r1, r2, n, l) ->
      Ertltree.Estore (r1, r2, n, l)
  | Rtltree.Emunop (op, r, l) ->
      Ertltree.Emunop (op, r, l)
  | Rtltree.Embinop (op, r1, r2, l) ->
      begin match op with
      | Mdiv ->
        let l_back = generate (Embinop (Mmov, Register.rax, r2, l)) in
        let l_div = generate (Embinop (Mdiv, r1, Register.rax, l_back)) in
        Embinop (Mmov, r2, Register.rax, l_div)
      | _ -> Embinop (op, r1, r2, l)
      end
  | Rtltree.Emubranch (b, r, l1, l2) ->
      Ertltree.Emubranch (b, r, l1, l2)
  | Rtltree.Embbranch (b, r1, r2, l1, l2) ->
      Ertltree.Embbranch (b, r1, r2, l1, l2)
  | Rtltree.Ecall (r, f, r_list, l) ->
      (* TODO *)
      Ertltree.Ecall (f, min (List.length r_list) 6, l)
  | Rtltree.Egoto l ->
      Ertltree.Egoto (l)

let rtl_to_ertl (l:Label.t) (i:Rtltree.instr) =
  let einstr = instr i in
  graph := Label.M.add l einstr !graph

let deffun (df:Rtltree.deffun) =
  graph := Label.M.add df.fun_exit Ertltree.Ereturn Label.M.empty;
  Label.M.iter rtl_to_ertl df.fun_body;
  {
    fun_name    = df.fun_name;
    fun_formals = Register.S.cardinal df.fun_locals;
    fun_locals  = df.fun_locals;
    fun_entry   = df.fun_entry;
    fun_body    = !graph;
  }

let program (file:Rtltree.file) =
  { funs = List.map deffun file.funs }
