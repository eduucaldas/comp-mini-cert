open Ertltree

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
      (* TODO *)
      | Mdiv -> Embinop (op, r1, r2, l)
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

let deffun (df:Rtltree.deffun) =
  {
    fun_name    = df.fun_name;
    fun_formals = Register.S.cardinal df.fun_locals;
    fun_locals  = df.fun_locals;
    fun_entry   = df.fun_entry;
    fun_body    = df.fun_body;
  }

let program (file:Rtltree.file) = {funs = List.map deffun file.funs}
