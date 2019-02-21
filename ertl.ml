open Ertltree

let instr = function
  | Rtltree.Econst (n, r, l) ->
      Econst (n, r, l)
  | _ -> Ereturn

let deffun (df:Rtltree.deffun) =
  {
    fun_name    = df.fun_name;
    fun_formals = Register.S.cardinal df.fun_locals;
    fun_locals  = df.fun_locals;
    fun_entry   = df.fun_entry;
    fun_body    = df.fun_body;
  }

let program (file:Rtltree.file) = {funs = List.map deffun file.funs}
