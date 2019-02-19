
open Ttree

(* utiliser cette exception pour signaler une erreur de typage *)
exception Error of string

(* we have to store the context in some way *)
type context = (Ttree.ident, Ttree.typ) Hashtbl.t

let (functions: (Ttree.ident, Ttree.typ * Ttree.typ list) Hashtbl.t) = Hashtbl.create 255

let (structs: (Ttree.ident, Ttree.structure) Hashtbl.t) = Hashtbl.create 255

let string_of_loc (l:(Lexing.position * Lexing.position)) =
  let file_of_pos (pos:Lexing.position) = if (String.equal pos.pos_fname "") then "" else " file:" ^ pos.pos_fname in
  let line_of_pos (pos:Lexing.position) = " line:" ^ (string_of_int pos.pos_lnum) in
  let col_of_pos (pos:Lexing.position) = " col:" ^ (string_of_int (pos.pos_cnum - pos.pos_bol)) in
  let pos1, pos2 = l in
  let sf1, sf2 = file_of_pos pos1, file_of_pos pos2 in
  let sl1, sl2 = line_of_pos pos1, line_of_pos pos2 in
  let sc1, sc2 = col_of_pos pos1, col_of_pos pos2 in
  "in" ^ sf1 ^ sl1 ^ sc1 ^  " -" ^ (
    if not (String.equal sf1 sf2) then sf2 ^ sl2 ^ sc2 else
    if not (String.equal sl1 sl2) then sl2 ^ sc2 else
   sc2)

let string_of_type = function
  | Tint       -> "int"
  | Tstructp x -> "struct " ^ x.str_name ^ " *"
  | Tvoidstar  -> "void*"
  | Ttypenull  -> "typenull"

let rec is_well_defined = function
  | Ptree.Tint -> true
  | Ptree.Tstructp s -> 
    if Hashtbl.mem structs s.id then true
    else false

let eq_of_type (t1:Ttree.typ) (t2:Ttree.typ) =
  (* QUESTION: fix struct equals 0 *)
  match (t1, t2) with
  | (Tint, Tint) | (Tint, Ttypenull) | (Ttypenull, Tint) -> true
  | (Tstructp s, Ttypenull) | (Ttypenull, Tstructp s) | (Tvoidstar, Tstructp s) | (Tstructp s, Tvoidstar) -> true
  | (Tvoidstar, Tvoidstar) -> true
  | (Ttypenull, Ttypenull) -> true
  | (Tstructp s1, Tstructp s2) -> String.equal s1.str_name s2.str_name
  | _ -> false

let cast_ident (id:Ptree.ident) =
  id.id

let rec type_expr (ctx: context) (expr: Ptree.expr) =
  (* TODO: fix col:-1 on error message *)
  let raise_expr_error msg = raise (Error ((string_of_loc expr.expr_loc) ^ " Type Error: " ^ msg)) in
  match expr.expr_node with
  | Ptree.Econst c -> {expr_typ = Tint; expr_node = Ttree.Econst c}
  | Ptree.Eright lv ->
    begin match lv with
      | Lident id ->
        let id_name = cast_ident id in
        if Hashtbl.mem ctx id_name then
          {expr_typ = Hashtbl.find ctx id_name; expr_node = Ttree.Eaccess_local id_name}
        else
          raise (Error ((string_of_loc id.id_loc) ^ " Type Error: variable " ^ id_name ^ " is not defined"))
      | Larrow (e, id) -> 
        (* e is of type Evalue on struct call *)
        let e_typed = type_expr ctx e in
        let field_name = cast_ident id in
        begin match e_typed.expr_typ with
          | Tstructp s ->
            if Hashtbl.mem s.str_fields field_name then
              let f  = Hashtbl.find s.str_fields field_name in
              {
                expr_typ = f.field_typ;
                expr_node = Ttree.Eaccess_field (e_typed, f)
              }
            else
              raise (Error ((string_of_loc id.id_loc) ^ " Type Error: struct field " ^ field_name ^ " is not well defined"))
          | _ -> raise (Error ((string_of_loc e.expr_loc) ^ " Type Error: expression is not a struct pointer"))
        end
    end
  | Ptree.Eassign (lv, e) ->
    let lv_typed = type_expr ctx {expr_node = Ptree.Eright (lv); expr_loc = expr.expr_loc} in
    let e_typed = type_expr ctx e in
    begin match lv_typed.expr_node with
    | Ttree.Eaccess_local id ->
      if eq_of_type lv_typed.expr_typ e_typed.expr_typ then
        {expr_typ = lv_typed.expr_typ; expr_node = Ttree.Eassign_local (id, e_typed)}
      else
      raise_expr_error ("variable " ^ id ^ " does not have a compatible type with the expression")
    | Ttree.Eaccess_field (e, f) ->
      if eq_of_type lv_typed.expr_typ e_typed.expr_typ then
        {expr_typ = lv_typed.expr_typ; expr_node = Ttree.Eassign_field (e, f, e_typed)}
      else
      raise_expr_error ("field " ^ f.field_name ^ " does not have a compatible type with the expression")
    | _ -> raise_expr_error ("incompatible left expression")
    end
  | Ptree.Eunop (op, e) ->
    let e_typed = type_expr ctx e in
    begin match op with
      | Unot ->
        {expr_typ = Tint; expr_node = Ttree.Eunop (Unot, e_typed)}
      | Uminus ->
        if eq_of_type e_typed.expr_typ Tint then
          {expr_typ = Tint; expr_node = Ttree.Eunop (Uminus, e_typed)}
        else
          raise_expr_error ("operator is not compatible with expression")
    end
  | Ptree.Ebinop (op, e1, e2) ->
    let e1_typed = type_expr ctx e1 in
    let e2_typed = type_expr ctx e2 in
    begin match op with
      | Beq | Bneq | Blt | Ble | Bgt | Bge ->
        if (eq_of_type e1_typed.expr_typ e2_typed.expr_typ) then
          {expr_typ = Tint; expr_node = Ttree.Ebinop (op, e1_typed, e2_typed)} else
            raise_expr_error "not yet implemented message"
      | Badd | Bsub | Bmul | Bdiv ->
        if (eq_of_type e1_typed.expr_typ Tint) && (eq_of_type e2_typed.expr_typ Tint) then
          {expr_typ = Tint; expr_node = Ttree.Ebinop (op, e1_typed, e2_typed)} else
            raise_expr_error "not yet implemented message"
      | Band | Bor ->
        {expr_typ = Tint; expr_node = Ttree.Ebinop (op, e1_typed, e2_typed)}
    end
  | Ptree.Ecall (id, e_list) ->
    if Hashtbl.mem functions (cast_ident id) then
      let (ret_type, formals_type) = Hashtbl.find functions (cast_ident id) in
      let e_list_typed = List.map (type_expr ctx) e_list in
      let e_type_list = List.map (fun e -> e.expr_typ) e_list_typed in
      try
      if List.fold_left2 (fun acc t1 t2 -> acc && eq_of_type t1 t2) true formals_type e_type_list then
        {expr_typ = ret_type;expr_node = Ttree.Ecall (cast_ident id, e_list_typed)}
      else raise_expr_error "not yet implemented message1"
      with Invalid_argument a -> raise_expr_error ("invalid arguments on function " ^  (cast_ident id))
    else raise_expr_error ("function: " ^ (cast_ident id))
  | Ptree.Esizeof id ->
    (* Not possible to do sizeof(int)? *)
    let name = cast_ident id in
    if Hashtbl.mem structs name then
      {expr_typ = Tint; expr_node = Ttree.Esizeof (Hashtbl.find structs name)}
    else
      raise (Error ((string_of_loc id.id_loc) ^ " Type Error: struct " ^ name ^ " was not defined"))


let type_typ = function
  | Ptree.Tint -> Ttree.Tint
  | Ptree.Tstructp s ->
    let id = cast_ident s in
    if Hashtbl.mem structs id then
      Ttree.Tstructp (Hashtbl.find structs id)
    else
      raise (Error ((string_of_loc s.id_loc) ^ " Type Error(decl_struct): struct " ^ id ^ " was not defined"))

let type_decl_var (dv:Ptree.decl_var) =
  let (t, id) = dv in (type_typ t, cast_ident id)

let type_decl_var_list (local_ctx: context) (dvl: Ptree.decl_var list) =
  let unique_set = Hashtbl.create 255 in
  let decl_var_list_typed = List.map type_decl_var dvl in
  let add_if_unique (t, id) =
    if Hashtbl.mem unique_set id then
      raise (Error "type error, not yet implemented message, not respecting unicity")
    else Hashtbl.add unique_set id true;
    Hashtbl.add local_ctx id t
  in
  List.iter add_if_unique decl_var_list_typed;
  decl_var_list_typed

let rec type_stmt (ctx: context) (ret_typ: Ttree.typ) (st: Ptree.stmt) =
  match st.stmt_node with
  | Sskip -> Ttree.Sskip
  | Sexpr e -> Ttree.Sexpr(type_expr ctx e)
  | Sif (e, s1, s2) ->
    let e_typed = type_expr ctx e in
    let s1_typed = type_stmt ctx ret_typ s1 in
    let s2_typed = type_stmt ctx ret_typ s2 in
    Ttree.Sif (e_typed, s1_typed, s2_typed)
  | Swhile (e, s) ->
    let e_typed = type_expr ctx e in
    let s_typed = type_stmt ctx ret_typ s in
    Ttree.Swhile (e_typed, s_typed)
  | Sblock b -> Ttree.Sblock(type_block ctx ret_typ b)
  | Sreturn e ->
    let e_typed = type_expr ctx e in
    if (eq_of_type e_typed.expr_typ ret_typ) then
      Ttree.Sreturn e_typed else
      raise (Error ((string_of_loc st.stmt_loc) ^ " Type Error(stmt): incoherent with return type"))

and type_block (ctx: context) (ret_typ: Ttree.typ) block =
  let local_ctx = Hashtbl.copy ctx in
  let (vars, sts) = block in
  let decl_vars_typed = type_decl_var_list local_ctx vars in
  let sts_typed = List.map (type_stmt local_ctx ret_typ) sts in
  (decl_vars_typed, sts_typed)

let add_function fun_name ret_type formals =
  let fun_name_cast = cast_ident fun_name in
  if Hashtbl.mem functions fun_name_cast then
  raise (Error ((string_of_loc fun_name.id_loc) ^ " Type Error(decl_fun): function " ^ fun_name_cast ^ " was already declared"))
  else
    let formals_type = List.map (fun (t, id) -> t) formals in
    Hashtbl.add functions fun_name_cast (ret_type, formals_type)

(* Attention, was VERY sleepy, check fun_body*)
(* Attention aux recursives *)
let type_decl_fun (ctx: context) (df: Ptree.decl_fun) =
  let fun_typ_typed = type_typ df.fun_typ in
  let fun_name_cast = cast_ident df.fun_name in
  let local_ctx = Hashtbl.copy ctx in
  let fun_formals_typed = type_decl_var_list local_ctx df.fun_formals in
  add_function df.fun_name fun_typ_typed fun_formals_typed;
  let fun_body_typed = type_block local_ctx fun_typ_typed df.fun_body in
  {
    fun_typ = fun_typ_typed;
    fun_name = fun_name_cast;
    fun_formals = fun_formals_typed;
    fun_body = fun_body_typed;
  }

let type_decl_struct ds =
  let ((id:Ptree.ident), (dvl:Ptree.decl_var list)) = ds in
  if Hashtbl.mem structs id.id then
    raise (Error ((string_of_loc id.id_loc) ^ " Type Error(decl_struct): struct " ^ id.id ^ " was already declared"))
  else
    let (fields: (Ttree.ident, Ttree.field) Hashtbl.t) = Hashtbl.create 255 in
    Hashtbl.add structs id.id {str_name = id.id; str_fields = fields};
    let valid_field (t, id) =
      if Hashtbl.mem fields (cast_ident id) then
        raise (Error ((string_of_loc id.id_loc) ^ " Type Error(decl_struct): struct field " ^ id.id ^ " was already declared"))
      else if is_well_defined t then
        Hashtbl.add fields (cast_ident id) {field_name = cast_ident id; field_typ = type_typ t}
      else
        raise (Error ((string_of_loc id.id_loc) ^ " Type Error(decl_struct): struct field " ^ id.id ^ " is not well defined"))
    in
    List.iter valid_field dvl;
    Hashtbl.replace structs id.id {str_name = id.id; str_fields = fields}


(* Performs typing on file AST produce via parsing
   Ptree.file -> exn Ttree.file *)
let rec type_file (ctx: context) = function
  | [] -> {funs = []}
  | (Ptree.Dfun f)::t -> 
    let f_typed = type_decl_fun ctx f in
    { funs = f_typed::((type_file ctx t).funs) }
  | (Ptree.Dstruct s)::t ->
    type_decl_struct s;
    type_file ctx t

let program (p:Ptree.file) =
  let ctx = Hashtbl.create 255 in
  type_file ctx p
