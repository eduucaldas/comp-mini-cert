
open Ttree

(* utiliser cette exception pour signaler une erreur de typage *)
exception Error of string

(* we have to store the context in some way *)
type context = (Ttree.ident, Ttree.typ) Hashtbl.t

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

let rec type_expr (ctx: context) = function
  | Ptree.Econst c -> {expr_typ = Tint; expr_node = Ttree.Econst c}
  | Ptree.Eunop (Unot, e) -> {expr_typ = Tint; expr_node = (type_expr ctx e.expr_node).expr_node}
  | Ptree.Eunop (Uminus, e) -> let expr_typed = type_expr ctx e.expr_node in 
                                if eq_of_type expr_typed.expr_typ Tint then
                                {expr_typ = Tint; expr_node = (type_expr ctx e.expr_node).expr_node}
                                else assert false
  | _ -> assert false

let cast_ident (id:Ptree.ident) =
  id.id

let type_typ = function
  | Ptree.Tint -> Ttree.Tint
  | _ -> assert false

let type_decl_var (dv:Ptree.decl_var) =
  let (t, id) = dv in (type_typ t, cast_ident id)

let rec type_stmt (ctx: context) (ret_typ: Ttree.typ) (st: Ptree.stmt) =
  match st.stmt_node with
  | Sreturn e ->
    let e_typed = type_expr ctx e.expr_node in
    if (eq_of_type e_typed.expr_typ ret_typ) then
      Ttree.Sreturn e_typed else
      assert false
  | Sblock b -> Ttree.Sblock(type_block ctx ret_typ b)
  | _ -> assert false

and type_block (ctx: context) (ret_typ: Ttree.typ) block =
  let (vars, sts) = block in
  let decl_vars_typed = List.map type_decl_var vars in
  let sts_typed = List.map (type_stmt ctx ret_typ) sts in
  (decl_vars_typed, sts_typed)


(* Attention aux recursives *)
let type_decl_fun (ctx: context) (df: Ptree.decl_fun) =
  let local_ctx = Hashtbl.copy ctx in
  let fun_typ_typed = type_typ df.fun_typ in
  let fun_name_cast = cast_ident df.fun_name in
  Hashtbl.add local_ctx fun_name_cast fun_typ_typed;
  let fun_formals_typed = List.map type_decl_var df.fun_formals in
  List.iter (fun (t, _) -> is_well_defined t) fun_formals_typed;
  let add_to_local formal =
    let (typ, id) = formal in
    Hashtbl.add local_ctx id typ;
  in
  List.iter add_to_local fun_formals_typed;
  let fun_body_typed = type_block local_ctx fun_typ_typed df.fun_body in
  Hashtbl.add ctx fun_name_cast fun_typ_typed;
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
