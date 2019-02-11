
open Ttree

(* utiliser cette exception pour signaler une erreur de typage *)
exception Error of string

(* we have to store the context in some way *)
type context = (Ttree.ident, Ttree.typ) Hashtbl.t

let (functions: (Ttree.ident, Ttree.typ * Ttree.typ list) Hashtbl.t) = Hashtbl.create 255

let string_of_loc (l:(Lexing.position * Lexing.position)) =
  let pos1, pos2 = l in
  let sf1, sf2 = pos1.pos_fname, pos2.pos_fname in
  let sl1, sl2 = string_of_int pos1.pos_lnum, string_of_int pos2.pos_lnum in
  let sc1, sc2 = string_of_int (pos1.pos_cnum - pos1.pos_bol), string_of_int (pos2.pos_cnum - pos2.pos_bol) in
  "in file:" ^ sf1 ^ " line:" ^ sl1 ^ " col:" ^ sc1  ^  " - " ^ (
    if not (String.equal sf1 sf2) then "file:" ^ sf2 ^ " line:" ^ sl2 ^ " col:" ^ sc2 else
    if not (String.equal sl1 sl2) then "line:" ^ sl2 ^ " col:" ^ sc2  else
    "col:" ^ sc2)

let string_of_type = function
  | Tint       -> "int"
  | Tstructp x -> "struct " ^ x.str_name ^ " *"
  | Tvoidstar  -> "void*"
  | Ttypenull  -> "typenull"

let rec is_well_defined = function
  | Tint | Tvoidstar | Ttypenull -> assert true
  | Tstructp s -> assert false

let eq_of_type t1 t2 =
  match (t1, t2) with
  | (Tint, Tint) -> true
  | _ -> assert false

let cast_ident (id:Ptree.ident) =
  id.id

let rec type_expr (ctx: context) (expr: Ptree.expr) =
  match expr.expr_node with
  | Ptree.Econst c -> {expr_typ = Tint; expr_node = Ttree.Econst c}
  | Ptree.Eright lv ->
    begin match lv with
      | Lident id ->
        let id_name = cast_ident id in
        if Hashtbl.mem ctx id_name then
          {expr_typ = Hashtbl.find ctx id_name; expr_node = Ttree.Eaccess_local id_name}
        else raise (Error "type error, not yet implemented message")
      | Larrow (e, id) -> assert false
    end
  | Ptree.Eassign (lv, e) ->
    let e_typed = type_expr ctx e in
    begin match lv with
      | Lident id ->
        let id_name = cast_ident id in
        if Hashtbl.mem ctx id_name && eq_of_type (Hashtbl.find ctx id_name) e_typed.expr_typ then
          {expr_typ = Hashtbl.find ctx id_name; expr_node = Ttree.Eassign_local (id_name, e_typed)}
        else raise (Error "type error, not yet implemented message")
      | Larrow (e, id) -> assert false
    end
  | Ptree.Eunop (op, e) ->
    let e_typed = type_expr ctx e in
    begin match op with
      | Unot ->
        {expr_typ = Tint; expr_node = Ttree.Eunop (Unot, e_typed)}
      | Uminus ->
        if eq_of_type e_typed.expr_typ Tint then
          {expr_typ = Tint; expr_node = Ttree.Eunop (Uminus, e_typed)} else
          assert false
    end
  | Ptree.Ebinop (op, e1, e2) ->
    let e1_typed = type_expr ctx e1 in
    let e2_typed = type_expr ctx e2 in
    begin match op with
      | Beq | Bneq | Blt | Ble | Bgt | Bge ->
        if (eq_of_type e1_typed.expr_typ e2_typed.expr_typ) then
          {expr_typ = Tint; expr_node = Ttree.Ebinop (op, e1_typed, e2_typed)} else
          raise (Error "type error, not yet implemented message")
      | Badd | Bsub | Bmul | Bdiv ->
        if (eq_of_type e1_typed.expr_typ Tint) && (eq_of_type e2_typed.expr_typ Tint) then
          {expr_typ = Tint; expr_node = Ttree.Ebinop (op, e1_typed, e2_typed)} else
          raise (Error "type error, not yet implemented message")
      | Band | Bor ->
        {expr_typ = Tint; expr_node = Ttree.Ebinop (op, e1_typed, e2_typed)}
    end
  | _ -> assert false

let type_typ = function
  | Ptree.Tint -> Ttree.Tint
  | _ -> assert false

let type_decl_var (dv:Ptree.decl_var) =
  let (t, id) = dv in (type_typ t, cast_ident id)

let type_decl_var_list (local_ctx: context) (dvl: Ptree.decl_var list) =
  let unique_set = Hashtbl.create 255 in
  let decl_var_list_typed = List.map type_decl_var dvl in
  let add_if_unique (t, id) =
    if Hashtbl.mem unique_set id then
      raise (Error "type error, not yet implemented message")
    else Hashtbl.add unique_set id true;
    Hashtbl.add local_ctx id t
  in
  List.iter add_if_unique decl_var_list_typed;
  decl_var_list_typed

let add_function name ret_type formals =
  if Hashtbl.mem functions name then
    raise (Error "type error, not yet implemented message")
  else
    let formals_type = List.map (fun (t, id) -> t) formals in
    Hashtbl.add functions name (ret_type, formals_type)

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
      raise (Error "Type Error(stmt): incoherent with return type:")

and type_block (ctx: context) (ret_typ: Ttree.typ) block =
  let local_ctx = Hashtbl.copy ctx in
  let (vars, sts) = block in
  let decl_vars_typed = type_decl_var_list local_ctx vars in
  let sts_typed = List.map (type_stmt local_ctx ret_typ) sts in
  (decl_vars_typed, sts_typed)

(* Attention, was VERY sleepy, check fun_body*)
(* Attention aux recursives *)
let type_decl_fun (ctx: context) (df: Ptree.decl_fun) =
  let fun_typ_typed = type_typ df.fun_typ in
  let fun_name_cast = cast_ident df.fun_name in
  if Hashtbl.mem ctx fun_name_cast then
    raise (Error ((string_of_loc df.fun_name.id_loc) ^ ": Type Error(decl_fun): function " ^ fun_name_cast ^ " was already declared"))
  else Hashtbl.add ctx fun_name_cast fun_typ_typed;
  let local_ctx = Hashtbl.copy ctx in
  let fun_formals_typed = type_decl_var_list local_ctx df.fun_formals in
  add_function fun_name_cast fun_typ_typed fun_formals_typed;
  let fun_body_typed = type_block local_ctx fun_typ_typed df.fun_body in
  {
    fun_typ = fun_typ_typed;
    fun_name = fun_name_cast;
    fun_formals = fun_formals_typed;
    fun_body = fun_body_typed;
  }

let type_decl (ctx: context) = function
  | Ptree.Dfun df -> type_decl_fun ctx df
  | _ -> assert false (* not yetimplemented *)

(* Performs typing on file AST produce via parsing
   Ptree.file -> exn Ttree.file *)
let rec type_file (ctx: context) = function
  | [] -> {funs = []}
  | h::t -> { funs = (type_decl ctx h)::((type_file ctx t).funs) }

let program p =
  let ctx = Hashtbl.create 255 in
  type_file ctx p
