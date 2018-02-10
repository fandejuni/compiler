open Ttree

(* utiliser cette exception pour signaler une erreur de typage *)
exception Error of string

let string_of_type = function
  | Tint       -> "int"
  | Tstructp x -> "struct " ^ x.str_name ^ " *"
  | Tvoidstar  -> "void*"
  | Ttypenull  -> "typenull"

type gamma_type = {
    variables : decl_var list;
    structs : structure list;
    functions : decl_fun list;
}

let add_var gamma decl_var =
{
    variables = decl_var::gamma.variables;
    structs = gamma.structs;
    functions = gamma.functions;
}

let add_structure gamma structure =
{
    variables = gamma.variables;
    structs = structure::gamma.structs;
    functions = gamma.functions;
}

let add_fun gamma decl_fun =
{
    variables = gamma.variables;
    structs = gamma.structs;
    functions = decl_fun::gamma.functions;
}

let add_var gamma decl_var =
{
    variables = decl_var::gamma.variables;
    structs = gamma.structs;
    functions = gamma.functions;
}

let create_expr typ expr_node =
{
	expr_typ = typ;
	expr_node = expr_node;
}

let compatible t1 t2 =
    match (t1, t2) with
    | (Ttypenull, _) -> true
    | (_, Ttypenull) -> true
    | (Tvoidstar, Tstructp(_)) -> true
    | (Tstructp(_), Tvoidstar) -> true
    | _ -> t1 = t2

let get_structure gamma str =
    let rec aux = function
    | [] -> raise(Error("Unknown structure"))
    | t::q -> if t.str_name = str then t else aux q
    in aux gamma.structs

let get_typ_var gamma str =
    let rec aux = function
    | [] -> raise(Error("Unknown variable"))
    | (typ, ident)::q -> if ident = str then typ else aux q
    in aux gamma.variables

let get_field expr ident =
    match expr.expr_typ with
    | Tstructp(structure) -> Hashtbl.find (structure.str_fields) ident 
    | _ -> raise(Error("Not a structure"))

let get_fun gamma str =
    let rec aux = function
    | [] -> raise(Error("Unknown function"))
    | f::q -> if f.fun_name = str then f else aux q
    in aux gamma.functions

let rec convert_expr (gamma: gamma_type) (expr: Ptree.expr) : gamma_type * expr =
    match expr.expr_node with
	| Ptree.Econst(i) when i = 0l -> (gamma, create_expr Ttypenull (Econst(0l)))
	| Ptree.Econst(i) -> (gamma, create_expr Tint (Econst(0l)))
    | Ptree.Eright(lv) ->
        begin
            match lv with
            | Ptree.Lident(ident) ->
                let str = ident.id in
                let typ = get_typ_var gamma str in
                (gamma, create_expr typ (Eaccess_local(ident.id)))
            | Ptree.Larrow(expr1, ident1) ->
                let (new_gamma, new_expr) = convert_expr gamma expr1 in
                let field = get_field new_expr (ident1.id) in
                (new_gamma, create_expr field.field_typ (Eaccess_field(new_expr, field)))
        end
    | Ptree.Eassign(lv, expr) ->
        let (new_gamma, big_expr) = convert_expr gamma expr in
        begin
            match lv with
            | Ptree.Lident(ident) ->
                let str = ident.id in
                let typ = get_typ_var new_gamma str in
                (gamma, create_expr typ (Eassign_local(ident.id, big_expr)))
            | Ptree.Larrow(expr1, ident1) ->
                let (new_new_gamma, new_expr) = convert_expr new_gamma expr1 in
                let field = get_field new_expr (ident1.id) in
                (new_new_gamma, create_expr field.field_typ (Eassign_field(new_expr, field, big_expr)))
        end
    | Eunop(unop, expr) when unop = Unot ->
        let (new_gamma, new_expr) = convert_expr gamma expr in
        (new_gamma, create_expr Tint (Eunop(unop, new_expr)))
    | Eunop(unop, expr) ->
        let (new_gamma, new_expr) = convert_expr gamma expr in
        if new_expr.expr_typ = Tint then
            (new_gamma, create_expr Tint (Eunop(unop, new_expr)))
        else
            raise(Error("- should be before an int"))
    | Ebinop(binop, expr1, expr2) ->
        let (gamma1, nexpr1) = convert_expr gamma expr1 in
        let (gamma2, nexpr2) = convert_expr gamma1 expr2 in
        begin
            match binop with
            | Band | Bor -> (gamma2, create_expr Tint (Ebinop(binop, nexpr1, nexpr2)))
            | Badd | Bsub | Bmul | Bdiv ->
                if nexpr1.expr_typ = Tint && nexpr2.expr_typ = Tint then
                    (gamma2, create_expr Tint (Ebinop(binop, nexpr1, nexpr2)))
                else
                    raise(Error("Bad type for + - / *"))
            | _ ->
                if compatible (nexpr1.expr_typ) (nexpr2.expr_typ) then
                    (gamma2, create_expr Tint (Ebinop(binop, nexpr1, nexpr2)))
                else
                    raise(Error("Uncompatible types"))
        end
    | Ecall(ident, expl) ->
        let f = get_fun gamma (ident.id) in
        begin
            let new_gamma = ref gamma in
            let rec aux a b =
                match (a, b) with
                | ([], []) -> []
                | (expr::q1, (typ, _)::q2) ->
                    let (temp_gamma, new_expr) = convert_expr (!new_gamma) expr in
                    new_gamma := temp_gamma;
                    if compatible typ (new_expr.expr_typ) then
                        new_expr::(aux q1 q2)
                    else
                        raise(Error("Argument not the right type"))
                | _ -> raise(Error("Mismatch in the number of arguments"))
            in  (!new_gamma, create_expr (f.fun_typ) (Ecall(ident.id, aux expl (f.fun_formals))))
        end
    | Esizeof(ident) ->
        let s = get_structure gamma (ident.id) in
        (gamma, create_expr Tint (Esizeof(s)))

let execute_structure gamma ((ident, decl_var_list):Ptree.decl_struct) : structure  =
    let table = Hashtbl.create 17 in
    let rec aux (l: Ptree.decl_var list) =
        match l with
        | [] -> ()
        | (Ptree.Tint, small_ident)::q -> Hashtbl.add table small_ident.id {field_name = small_ident.id; field_typ = Tint}; aux q
        | (Ptree.Tstructp(other_ident), small_ident)::q ->
            let s = get_structure gamma (other_ident.id) in
            Hashtbl.add table small_ident.id {field_name = small_ident.id; field_typ = Tstructp(s)}; aux q
    in aux decl_var_list;
    {
        str_name = ident.id;
        str_fields = table;
    }

let execute_function gamma decl_fun : gamma_type * decl_fun =
    raise(Error("To be implemented"))

let program file = 
    let rec aux gamma = function
    | [] -> gamma
    | Ptree.Dstruct(decl_struct)::q ->
        let structure = execute_structure gamma decl_struct in
        aux (add_structure gamma structure) q
    | Ptree.Dfun(decl_fun)::q ->
        let (new_gamma, fonction) = execute_function gamma decl_fun in
        aux (add_fun new_gamma fonction) q
    in {funs = (aux {variables = []; structs = []; functions = []} file).functions}
