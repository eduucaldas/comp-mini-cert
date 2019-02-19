open Rtltree

let graph = ref Label.M.empty

let generate i =
  let l = Label.fresh () in
  graph := Label.M.add l i !graph;
  l

let binop_to_as = function
  | Ptree.Badd -> Ops.Madd
  | Ptree.Bsub -> Ops.Msub
  | Ptree.Bmul -> Ops.Mmul
  | Ptree.Bdiv -> Ops.Mdiv
  | Ptree.Beq  -> Ops.Msete
  | Ptree.Bneq -> Ops.Msetne
  | Ptree.Bge  -> Ops.Msetge
  | Ptree.Ble  -> Ops.Msetle
  | Ptree.Bgt  -> Ops.Msetg
  | Ptree.Blt  -> Ops.Msetl
  | _ -> assert false


let rec condition (e:Ttree.expr) l_true l_false locals =
  let r_tmp = Register.fresh () in
  let destl = generate (Rtltree.Emubranch(Mjnz, r_tmp, l_true, l_false)) in
  expr e r_tmp destl locals

and expr (e:Ttree.expr) destr destl locals =
  match e.expr_node with
  | Ttree.Econst c -> generate (Rtltree.Econst(c, destr, destl))
  | Ttree.Eunop (Ptree.Uminus, e) ->
    let r_tmp = Register.fresh () in
    let l_unop = generate (Rtltree.Embinop(Ops.Msub, r_tmp, destr, destl)) in
    let l_zero = generate (Rtltree.Econst(Int32.zero, destr, l_unop)) in
    expr e r_tmp l_zero locals
  | Ttree.Eunop (Ptree.Unot, e) ->
    let l_not = generate (Rtltree.Emunop(Ops.Msetei(Int32.zero), destr, destl)) in
    expr e destr l_not locals
  | Ttree.Ebinop (Ptree.Badd | Ptree.Bsub | Ptree.Bmul
                 | Ptree.Bdiv | Ptree.Beq | Ptree.Bneq | Ptree.Bge
                 | Ptree.Bgt | Ptree.Ble | Ptree.Blt as b, e1, e2)  ->
    let r_tmp = Register.fresh () in
    let l_binop = generate (Rtltree.Embinop((binop_to_as b), r_tmp, destr, destl)) in
    let l_r = expr e2 r_tmp l_binop locals in
    expr e1 destr l_r locals
  | Ttree.Ebinop (Ptree.Band | Ptree.Bor as b, e1, e2) ->
    let l_continue = expr e2 destr destl locals in
    let l_stop = expr e1 destr destl locals in
    (match b with
     | Ptree.Band -> condition e1 l_continue l_stop locals
     | Ptree.Bor -> condition e1 l_stop l_continue locals
     | _ -> assert false
    )
  | Ttree.Eassign_local (id, e) ->
    let r_tmp = Register.fresh () in
    let r_id = Hashtbl.find locals id in
    let l_store = generate (Rtltree.Embinop(Mmov, r_tmp, r_id, destl)) in
    expr e r_tmp l_store locals
  | Ttree.Eaccess_local id ->
    let r_id = Hashtbl.find locals id in
    generate (Rtltree.Embinop(Mmov, r_id, destr, destl))
  | _ -> assert false

let rec stmt (s:Ttree.stmt) destl retr exitl locals =
  match s with
  | Ttree.Sskip -> destl
  | Ttree.Sexpr e -> let r = Register.fresh () in expr e r destl locals
  | Ttree.Sif (e, s_true, s_false) ->
    let l_true = stmt s_true destl retr exitl locals in
    let l_false = stmt s_false destl retr exitl locals in
    condition e l_true l_false locals
  | Ttree.Sblock (dv_list, s_list) -> (
      let rec stmt_list = function
        | [] -> destl
        | h::t -> stmt h (stmt_list t) retr exitl locals
      in
      stmt_list s_list
    )
  | Ttree.Sreturn e -> expr e retr exitl locals
  | _ -> assert false


let deffun (df:Ttree.decl_fun) =
  graph := Label.M.empty;
  let exitl = Label.fresh () in
  let retr = Register.fresh () in
  let local_regs = Hashtbl.create 255 in
  let allocate_register dv =
    let reg = Register.fresh () in
    Hashtbl.add local_regs (snd dv) reg;
    reg
  in
  let formals = List.map allocate_register df.fun_formals in
  let body_local_vars = List.map allocate_register (fst df.fun_body) in
  let locals = Register.set_of_list (formals@body_local_vars) in
  let entry = stmt (Ttree.Sblock(df.fun_body)) exitl retr exitl local_regs in
  {
    fun_name = df.fun_name;
    fun_formals = formals;
    fun_result = retr;
    fun_locals = locals;
    fun_exit = exitl;
    fun_entry = entry;
    fun_body = !graph;
  }

let program (file:Ttree.file) = {funs = List.map deffun file.funs}

