
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

let rec gamma_mem x = function
    | [] -> false
    | t::q -> t.str_name = x || gamma_mem x q

let check_type gamma = function
    | Tint -> true
    | Tstructp(ident) -> gamma_mem ident gamma

(* gamma: structure list *)

(* TODO: check si deux identifiants égaux *)
let rec struct_bien_formee gamma = function
    | [] -> true
    | (typ, ident)::q -> check_type gamma typ && struct_bien_formee gamma q

let check_function decl_fun gamma =
    let b1 = check_type gamma decl_fun.typ in
    let b2 = 
    

let jugement gamma = function
    | Dstruct((ident, decl_list)) -> if (struct_bien_formee gamma decl_list) && (not (gamma_mem ident gamma)) then
        (ident, decl_list)::gamma
    else
        raise Error("Structure mal formée ou type existant")
    | Dfun(decl_fun) -> if (check_function decl_fun gamma) then ...


