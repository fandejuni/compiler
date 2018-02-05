open Ttree

(* utiliser cette exception pour signaler une erreur de typage *)
exception Error of string

let string_of_type = function
  | Tint       -> "int"
  | Tstructp x -> "struct " ^ x.str_name ^ " *"
  | Tvoidstar  -> "void*"
  | Ttypenull  -> "typenull"

type gamma_type = {
    structs : Ptree.decl_struct list;
    functions : Ptree.decl_fun list
}
(* gamma:
    * gamma.struct = structure list
    * gamma.functions = decl_fun list
    *)

let gamma_structure_mem x (gamma: gamma_type) =
    let rec aux (l: Ptree.decl_struct list) =
    match l with
    | [] -> false
    | (name, _)::q -> name.id = x || (aux q)
    in aux gamma.structs

let check_type gamma = function
    | Ptree.Tint -> true
    | Ptree.Tstructp(ident) -> gamma_structure_mem ident.id gamma

(* TODO: check si deux identifiants égaux *)
let rec struct_bien_formee gamma = function
    | [] -> true
    | (typ, ident)::q -> check_type gamma typ && struct_bien_formee gamma q

let rec check_arguments gamma = function
    | [] -> true
    | (typ, _)::q -> check_type gamma typ && check_arguments gamma q


let rec check_expr_sans_type gamma env (exp : Ptree.expr) = 
    (* TODO *)
    match exp.expr_node with
    | Econst(i) -> true
    | _ -> false  
   (* | Eright of lvalue
    | Eassign of lvalue * expr
    | Eunop of unop * expr
    | Ebinop of binop * expr * expr
    | Ecall of ident * expr list
    | Esizeof of ident
    *)
let rec check_expr gamma env (exp : Ptree.expr) typ = 
    (* TODO *)
    match exp.expr_node with
    | Econst(0l) -> true
    | Econst(i) -> false 
    | _ -> false  
   (* | Eright of lvalue
    | Eassign of lvalue * expr
    | Eunop of unop * expr
    | Ebinop of binop * expr * expr
    | Ecall of ident * expr list
    | Esizeof of ident
    *)

let rec check_statement gamma env (stmt: Ptree.stmt) ret_type =
(* TODO *)
    match stmt.stmt_node with
	| Ptree.Sskip -> true
	| Ptree.Sexpr(exp) -> check_expr_sans_type gamma env exp
	| Ptree.Sif (exp, stmt1, stmt2) -> (check_expr gamma env exp Tint) && (check_statement gamma env stmt1 ret_type) && (check_statement gamma env stmt2 ret_type)
	| Ptree.Swhile (exp,stmt1) -> (check_expr gamma env exp Tint) && (check_statement gamma env stmt1 ret_type)
	| Ptree.Sblock (bloc)-> check_body gamma env bloc ret_type
	| Ptree.Sreturn (exp) -> check_expr gamma env exp ret_type 
and check_statements gamma env ret_type = function
    | [] -> true
    | t::q -> check_statement gamma env t ret_type && check_statements gamma env ret_type q
and check_body gamma env (vars, stmts) (ret_type: Ptree.typ) =
    if check_arguments gamma vars then
        let new_env = vars@env in
        check_statements gamma new_env ret_type stmts
    else
        raise(Error("Déclaration de variables illégale"))

let add_fun gamma (f: Ptree.decl_fun) =
    {
        structs = gamma.structs;
        functions = f::gamma.functions
    }

let add_struct gamma s =
    {
        structs = s::gamma.structs;
        functions = gamma.functions
    }

let check_function (decl_fun: Ptree.decl_fun) gamma =
    let b1 = check_type gamma decl_fun.fun_typ in
    let b2 = check_arguments gamma decl_fun.fun_formals in
    let gamma_prime = add_fun gamma decl_fun in
    let b3 = check_body gamma_prime decl_fun.fun_formals decl_fun.fun_body decl_fun.fun_typ in
    b1 && b2 && b3

let jugement gamma = function
    | Ptree.Dstruct((ident, decl_list)) -> if (struct_bien_formee gamma decl_list) && (not (gamma_structure_mem ident.id gamma)) then
        add_struct gamma (ident, decl_list)
    else
        raise(Error("Structure mal formée ou type existant"))
    | Ptree.Dfun(decl_fun) -> if (check_function decl_fun gamma) then
        add_fun gamma decl_fun
    else
        raise(Error("Fonction mal déclarée"))

let convert_type gamma (typ: Ptree.typ) : Ttree.typ =
    raise(Error("Not cool"))

let get_type_expr_node gamma expr_node : typ =
    raise(Error("Not cool"))

let convert gamma p =
    (*let convert_expr = funct *)
    let convert_stmt_node = function
		| Ptree.Sskip -> Sskip
		| Ptree.Sexpr(expr) -> Sskip
		| Ptree.Sif(expr, stmt1, stmt2) -> Sskip
		| Ptree.Swhile(expr, stmt) -> Sskip
		| Ptree.Sblock(block) -> Sskip
		| Ptree.Sreturn(expr) -> Sskip
    in
    let convert_stmt (stmt: Ptree.stmt) =
        convert_stmt_node stmt.stmt_node
    in
    let convert_var ((typ, ident): Ptree.decl_var) =
        (convert_type gamma typ, ident.id)
    in
    let convert_block ((decl_var_list, stmt_list): Ptree.block) =
        (List.map convert_var decl_var_list), (List.map convert_stmt stmt_list)
    in
    let convert_fun (f: Ptree.decl_fun) =
    {
        fun_typ = convert_type gamma f.fun_typ;
        fun_name = f.fun_name.id;
        fun_formals = List.map convert_var f.fun_formals;
        fun_body = convert_block f.fun_body
    }
    in
    let rec convert_p = function
    | [] -> []
    | (Ptree.Dfun(decl_fun)::q) -> (convert_fun decl_fun)::(convert_p q)
    | t::q -> convert_p q
    in
    convert_p p

let program p =
   let rec aux gamma = function
    | [] -> gamma
    | t::q -> aux (jugement gamma t) q
    in let gamma_vide = {
        structs = [];
        functions = []
    }
    in convert (aux gamma_vide p) p
