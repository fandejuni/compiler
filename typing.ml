
open Ttree

(* utiliser cette exception pour signaler une erreur de typage *)
exception Error of string

let string_of_type = function
  | Tint       -> "int"
  | Tstructp x -> "struct " ^ x.str_name ^ " *"
  | Tvoidstar  -> "void*"
  | Ttypenull  -> "typenull"

let program p =
    assert("Failure")

let gamma_structure_mem x gamma =
    let rec aux = function
    | [] -> false
    | t::q -> t.str_name = x || aux x q
    in aux gamma.structs

let check_type gamma = function
    | Tint -> true
    | Tstructp(ident) -> gamma_structure_mem ident gamma

(* gamma: structure list *)

(* TODO: check si deux identifiants égaux *)
let rec struct_bien_formee gamma = function
    | [] -> true
    | (typ, ident)::q -> check_type gamma typ && struct_bien_formee gamma q

let rec check_arguments gamma = function
    | [] -> true
    | (typ, _)::q -> check_type gamma typ && check_arguments gamma q

let rec check_statement gamma env stmt =
(* TODO *)
    match stmt.stmt_node with
	| Sskip -> true
	| Sexpr(expr) ->
	| Sif of expr * stmt * stmt
	| Swhile of expr * stmt
	| Sblock of block
	| Sreturn of expr


let rec check_statements gamma env = function
    | [] -> true
    | t::q -> check_statement gamma env stmt && check_statements gamma env q

let check_body gamma env (vars, stmts) =
    if check_arguments gamma vars then
        let new_env = vars@env in
        check_statements gamma new_env stmts
    else
        raise Error("Déclaration de variables illégale")

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
    let b3 = check_body gamma_prime fun_formals in
    b1 && b2 && b3
    
(* gamma:
    * gamma.struct = structure list
    * gamma.functions = decl_fun list
    *)

let jugement gamma env_function = function
    | Dstruct((ident, decl_list)) -> if (struct_bien_formee gamma decl_list) && (not (gamma_structure_mem ident gamma)) then
        add_struct gamma (ident, decl_list)
    else
        raise Error("Structure mal formée ou type existant")
    | Dfun(decl_fun) -> if (check_function decl_fun gamma) then
        add_fun gamma decl_fun
    else
        raise Error("Fonction mal déclarée")


