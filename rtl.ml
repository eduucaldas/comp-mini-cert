open Rtltree

let graph = ref Label.M.empty

let generate i =
  let l = Label.fresh () in
  graph := Label.M.add l i !graph;
  l

let rec expr (e:Ttree.expr) destr destl =
  match e.expr_node with
  | Ttree.Econst c -> generate (Rtltree.Econst(c, destr, destl))
  | _ -> assert false

let rec stmt (s:Ttree.stmt) destl retr exitl =
  match s with
  | Ttree.Sreturn e -> expr e retr exitl
  | Ttree.Sblock (dv_list, s_list) -> (
      let rec stmt_list = function
        | [] -> destl
        | h::t -> stmt h (stmt_list t) retr exitl
      in
      stmt_list s_list
    )
  | _ -> assert false


let deffun (df:Ttree.decl_fun) =
  graph := Label.M.empty;
  let exitl = Label.fresh () in
  let retr = Register.fresh () in
  let entry = stmt (Ttree.Sblock(df.fun_body)) exitl retr exitl in
  let formals = List.map (fun x -> Register.fresh ()) df.fun_formals in
  let locals = Register.set_of_list formals in
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

