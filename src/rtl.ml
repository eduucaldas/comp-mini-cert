open Rtltree

let graph = ref Label.M.empty

let local_vars = Hashtbl.create 255

let locals = ref []

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


let rec condition (e:Ttree.expr) l_true l_false =
  let r_tmp = Register.fresh () in
  let destl = generate (Rtltree.Emubranch(Mjnz, r_tmp, l_true, l_false)) in
  expr e r_tmp destl

and expr (e:Ttree.expr) destr destl =
  match e.expr_node with
  | Ttree.Econst c -> generate (Rtltree.Econst(c, destr, destl))
  | Ttree.Eunop (Ptree.Uminus, e) ->
    let r_tmp = Register.fresh () in
    let l_unop = generate (Rtltree.Embinop(Ops.Msub, r_tmp, destr, destl)) in
    let l_zero = generate (Rtltree.Econst(Int32.zero, destr, l_unop)) in
    expr e r_tmp l_zero
  | Ttree.Eunop (Ptree.Unot, e) ->
    let l_not = generate (Rtltree.Emunop(Ops.Msetei(Int32.zero), destr, destl)) in
    expr e destr l_not
  | Ttree.Ebinop (Ptree.Badd | Ptree.Bsub | Ptree.Bmul
                 | Ptree.Bdiv | Ptree.Beq | Ptree.Bneq | Ptree.Bge
                 | Ptree.Bgt | Ptree.Ble | Ptree.Blt as b, e1, e2)  ->
    let r_tmp = Register.fresh () in
    let l_binop = generate (Rtltree.Embinop((binop_to_as b), r_tmp, destr, destl)) in
    let l_r = expr e2 r_tmp l_binop in
    expr e1 destr l_r
  | Ttree.Ebinop (Ptree.Band | Ptree.Bor as b, e1, e2) ->
    let l_true = generate (Rtltree.Econst(Int32.one, destr, destl)) in
    let l_false = generate (Rtltree.Econst(Int32.zero, destr, destl)) in
    let l_continue = condition e2 l_true l_false in
    (match b with
     | Ptree.Band -> condition e1 l_continue l_false
     | Ptree.Bor -> condition e1 l_true l_continue
     | _ -> assert false
    )
  | Ttree.Eassign_local (id, e) ->
    let r_id = Hashtbl.find local_vars id in
    let l_store = generate (Rtltree.Embinop(Mmov, destr, r_id, destl)) in
    expr e destr l_store
  | Ttree.Eassign_field (e1, f, e2) ->
    let r2 = Register.fresh () in
    let l_assign = generate (Rtltree.Estore (r2, destr, f.field_pos, destl)) in
    let l2 = expr e2 r2 l_assign in
    expr e1 destr l2
  | Ttree.Eaccess_local id ->
    let r_id = Hashtbl.find local_vars id in
    generate (Rtltree.Embinop(Mmov, r_id, destr, destl))
  | Ttree.Eaccess_field (e, f) ->
    let r_tmp = Register.fresh () in
    let l_access = generate (Rtltree.Eload (r_tmp, f.field_pos, destr, destl)) in
    expr e r_tmp l_access
  | Ttree.Ecall (id, e_list) ->
    let r_list = List.rev_map (fun x -> Register.fresh ()) e_list in
    let l_fun = generate (Rtltree.Ecall (destr, id, r_list, destl)) in
    let eval_parameter exp reg l_temp =
      expr exp reg l_temp
    in
    List.fold_right2 eval_parameter e_list r_list l_fun
  | Ttree.Esizeof s -> generate (Rtltree.Econst(Int32.of_int s.str_size, destr, destl))

let rec stmt (s:Ttree.stmt) destl retr exitl =
  match s with
  | Ttree.Sskip -> destl
  | Ttree.Sexpr e -> let r = Register.fresh () in expr e r destl
  | Ttree.Sif (e, s_true, s_false) ->
    let l_true = stmt s_true destl retr exitl in
    let l_false = stmt s_false destl retr exitl in
    condition e l_true l_false
  | Ttree.Swhile (e, s) ->
    let l_decision = Label.fresh () in
    let l_s = stmt s l_decision retr exitl in
    let l_condition = condition e l_s destl in
    graph := Label.M.add l_decision (Label.M.find l_condition !graph) !graph;
    generate (Rtltree.Egoto l_decision)
  | Ttree.Sblock (dv_list, s_list) ->
      let allocate_local_register dv =
        let r = Register.fresh () in
        Hashtbl.add local_vars (snd dv) r;
        locals := r :: !locals
      in
      List.iter allocate_local_register dv_list;
      let rec stmt_list = function
        | [] -> destl
        | h::t -> stmt h (stmt_list t) retr exitl
      in
      let free_variable dv =
        Hashtbl.remove local_vars (snd dv)
      in
      let l_block = stmt_list s_list in
      List.iter free_variable dv_list;
      l_block
  | Ttree.Sreturn e -> expr e retr exitl

let deffun (df:Ttree.decl_fun) =
  graph := Label.M.empty;
  Hashtbl.reset local_vars;
  locals := [];
  let exitl = Label.fresh () in
  let retr = Register.fresh () in
  let allocate_register dv =
    let r = Register.fresh () in
    Hashtbl.add local_vars (snd dv) r;
    r
  in
  let formals = List.map allocate_register df.fun_formals in
  let entry = stmt (Ttree.Sblock(df.fun_body)) exitl retr exitl in
  {
    fun_name = df.fun_name;
    fun_formals = formals;
    fun_result = retr;
    fun_locals = Register.set_of_list !locals;
    fun_exit = exitl;
    fun_entry = entry;
    fun_body = !graph;
  }

let program (file:Ttree.file) = {funs = List.map deffun file.funs}

