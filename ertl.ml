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
    let n_of_stack_params = max 0 (List.length r_list - 6) in
    let l_pop =
      if n_of_stack_params == 0 then l
      else
        generate (Emunop (Maddi(Int32.of_int (-8 * n_of_stack_params)), Register.rsp, l))
    in
    let l_ret = generate (Embinop (Mmov, Register.result, r, l_pop)) in
    let ertl_call = Ecall (f, min (List.length r_list) 6, l_ret) in
    let rec pass_args i r_l ertl =
        match r_l with
        | [] -> ertl
        | r_h::r_t ->
          let next_ertl = (pass_args (i + 1) r_t ertl) in
          let next_lab = generate next_ertl in
            if i < 6 then
              Embinop (Mmov, r_h, List.nth Register.parameters i, next_lab)
            else
              Epush_param (r_h, next_lab)
      in
      pass_args 0 r_list ertl_call
  | Rtltree.Egoto l ->
      Ertltree.Egoto (l)

let rtl_to_ertl (l:Label.t) (i:Rtltree.instr) =
  let einstr = instr i in
  graph := Label.M.add l einstr !graph

let deffun (df:Rtltree.deffun) =
  graph := Label.M.empty;
  let l_ret = generate (Ertltree.Ereturn) in

  (* delete frame *)
  let l_del_frame = generate (Ertltree.Edelete_frame (l_ret)) in
  let r_callees = List.map (fun x -> Register.fresh ()) Register.callee_saved in
  let l_load_callee = List.fold_right2
      (fun r_source r_dest l -> generate (Ertltree.Embinop(Mmov, r_source, r_dest, l)))
      r_callees Register.callee_saved l_del_frame in

  (* return value into rax *)
  graph := Label.M.add df.fun_exit
      (Ertltree.Embinop(Mmov, df.fun_result, Register.result, l_load_callee)) !graph;

  (* body instructions *)
  Label.M.iter rtl_to_ertl df.fun_body;

  (* Get parameters from rdi,rsi etc*)
  let rec recover_args i r_l l =
    match r_l with
    | [] -> l
    | r_h::r_t ->
      let l_next = (recover_args (i + 1) r_t l) in
      generate (
        if i < 6 then
          Embinop (Mmov, List.nth Register.parameters i, r_h, l_next)
        else
          Eget_param (-8 * (i - 6), r_h, l)
      )
  in
  let l_args = recover_args 0 df.fun_formals df.fun_entry in
  (* alloc_frame *)
  let l_store_callee = List.fold_right2
      (fun r_source r_dest l -> generate (Ertltree.Embinop(Mmov, r_source, r_dest, l)))
      Register.callee_saved r_callees l_args in
  let l_entry = generate (Ertltree.Ealloc_frame (l_store_callee)) in

  {
    fun_name    = df.fun_name;
    fun_formals = List.length df.fun_formals;
    fun_locals  = Register.S.union df.fun_locals (Register.set_of_list r_callees);
    fun_entry   = l_entry;
    fun_body    = !graph;
  }

let program (file:Rtltree.file) =
  { funs = List.map deffun file.funs }
