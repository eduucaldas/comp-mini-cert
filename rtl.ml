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
  | _ -> assert false

let rec expr (e:Ttree.expr) destr destl locals =
  match e.expr_node with
  | Ttree.Econst c -> generate (Rtltree.Econst(c, destr, destl))
  | Ttree.Eunop (Ptree.Uminus, e) ->
    let r_tmp = Register.fresh () in
    let l_unop = generate (Rtltree.Embinop(Ops.Msub, r_tmp, destr, destl)) in
    let l_r_minus = expr e r_tmp l_unop locals in
    generate (Rtltree.Embinop(Ops.Msub, destr, destr, l_r_minus))
  | Ttree.Ebinop (Ptree.Badd | Ptree.Bsub | Ptree.Bmul | Ptree.Bdiv as b,
                                                         e1, e2)  ->
    let r_tmp = Register.fresh () in
    let l_binop = generate (Rtltree.Embinop((binop_to_as b), r_tmp, destr, destl)) in
    let l_r = expr e2 r_tmp l_binop locals in
    expr e1 destr l_r locals
  | Ttree.Eassign_local (id, e) ->
    let r_tmp = Register.fresh () in
    let l_store = generate (Rtltree.Estore(r_tmp, Hashtbl.find locals id, 0, destl)) in
    expr e r_tmp l_store locals
  | _ -> assert false

let rec stmt (s:Ttree.stmt) destl retr exitl locals =
  match s with
  | Ttree.Sreturn e -> expr e retr exitl locals
  | Ttree.Sexpr e -> expr e retr destl locals
  | Ttree.Sblock (dv_list, s_list) -> (
      let rec stmt_list = function
        | [] -> destl
        | h::t -> stmt h (stmt_list t) retr exitl locals
      in
      stmt_list s_list
    )
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

