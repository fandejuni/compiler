open Ttree

(* utiliser cette exception pour signaler une erreur de typage *)
exception Error of string

let string_of_type = function
  | Tint       -> "int"
  | Tstructp x -> "struct " ^ x.str_name ^ " *"
  | Tvoidstar  -> "void*"
  | Ttypenull  -> "typenull"
type gamma_type = {
    structs : structure list;
    functions : decl_fun list
}
(* gamma:
    * gamma.struct = structure list
    * gamma.functions = decl_fun list
    *)

let gamma_structure_mem x gamma =
    let rec aux = function
    | [] -> false
    | t::q -> t.str_name = x || (aux q)
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
	| Ptree.Sreturn (exp) -> check_expr gamma env ret_type exp
and check_statements gamma env ret_type = function
    | [] -> true
    | t::q -> check_statement gamma env t ret_type && check_statements gamma env ret_type q
and check_body gamma env (vars, stmts) ret_type =
    if check_arguments gamma vars then
        let new_env = vars@env in
        check_statements gamma new_env ret_type stmts
    else
        raise(Error("Déclaration de variables illégale"))

let add_fun gamma f =
    {
        structs = gamma.structs;
        functions = f::gamma.functions
    }

let add_struct gamma s =
    {
        structs = s::gamma.structs;
        functions = gamma.functions
    }

let check_function decl_fun gamma =
    let b1 = check_type gamma decl_fun.typ in
    let b2 = check_arguments gamma decl_fun.fun_formals in
    let gamma_prime = add_fun gamma f in
    let b3 = check_body gamma_prime fun_formals decl_fun.typ in
    b1 && b2 && b3
    


let jugement gamma env_function = function
    | Dstruct((ident, decl_list)) -> if (struct_bien_formee gamma decl_list) && (not (gamma_structure_mem ident gamma)) then
        add_struct gamma (ident, decl_list)
    else
        raise Error("Structure mal formée ou type existant")
    | Dfun(decl_fun) -> if (check_function decl_fun gamma) then
        add_fun gamma decl_fun
    else
        raise Error("Fonction mal déclarée")

let program p =
    let gamma = {
        structs = [];
        functions = []
    } and env = []
    in 
    jugement gamma env p
