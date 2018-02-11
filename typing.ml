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
    ret_typ : typ;
}

let unique l =
    let rec aux accu = function
    | [] -> true
    | t::q -> if (List.mem t accu) then false
    else aux (t::accu) q
    in aux [] l

let reset_env gamma =
    {
        variables = [];
        structs = gamma.structs;
        functions = gamma.functions;
        ret_typ = gamma.ret_typ;
    }

let add_structure gamma structure =
    let l = structure::gamma.structs in
    if unique l then
    {
        variables = gamma.variables;
        structs = l;
        functions = gamma.functions;
        ret_typ = gamma.ret_typ;
    }
    else
        raise(Error("Twice the same structure"))

let add_fun gamma decl_fun =
    let l = decl_fun::gamma.functions in
    if unique l then
    {
        variables = gamma.variables;
        structs = gamma.structs;
        functions = l;
        ret_typ = gamma.ret_typ;
    }
    else
        raise(Error("Twice the same function"))

let add_to_env gamma decl_var_list : gamma_type =
    {
        variables = decl_var_list@gamma.variables;
        structs = gamma.structs;
        functions = gamma.functions;
        ret_typ = gamma.ret_typ;
    }

let set_ret_type gamma typ =
{
    variables = gamma.variables;
    structs = gamma.structs;
    functions = gamma.functions;
    ret_typ = typ;
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
    | [] -> raise(Error("Unknown variable: " ^ str ^ "\n"))
    | (typ, ident)::q -> if ident = str then typ else aux q
    in aux gamma.variables

let get_field expr ident =
    match expr.expr_typ with
    | Tstructp(structure) -> Hashtbl.find (structure.str_fields) ident 
    | _ -> raise(Error("Not a structure"))

let get_fun gamma str =
    let rec aux = function
    | [] -> raise(Error("Unknown function: " ^ str))
    | f::q -> if f.fun_name = str then f else aux q
    in aux gamma.functions

let convert_typ gamma = function
    | Ptree.Tint -> Tint
    | Ptree.Tstructp(ident) -> 
        let s = get_structure gamma (ident.id) in
        Tstructp(s)

let convert_decl_var gamma ((typ, ident): Ptree.decl_var) : decl_var =
    (convert_typ gamma typ, ident.id)

let convert_list gamma (decl_var_list: Ptree.decl_var list) : decl_var list =
    let l = List.map (convert_decl_var gamma) decl_var_list in
    if unique (List.map snd l) then
        l
    else
        raise(Error("Twice the same name of variable in list of declarations"))

let rec convert_block gamma ((old_decl_var_list, stmt_list):Ptree.block) : block =
    let decl_var_list = convert_list gamma old_decl_var_list in
    let gamma1 = add_to_env gamma decl_var_list in
    let rec aux gamma2 =  function
    | [] -> []
    | stmt::q -> let (gamma3, stmt2) = convert_stmt gamma2 stmt in
        stmt2::(aux gamma3 q)
    in (decl_var_list, aux gamma1 stmt_list)
and convert_stmt gamma (stmt: Ptree.stmt) : gamma_type * stmt =
    match stmt.stmt_node with
    | Ptree.Sskip -> (gamma, Sskip)
    | Ptree.Sexpr(expr) -> let (new_gamma, new_expr) = convert_expr gamma expr in
        (new_gamma, Sexpr(new_expr))
    | Ptree.Sif(expr, stmt1, stmt2) -> 
        let (gamma1, new_expr) = convert_expr gamma expr in
        (* TODO: check if statements same types? *)
        let (gamma2, new_stmt1) = convert_stmt gamma1 stmt1 in
        let (gamma3, new_stmt2) = convert_stmt gamma2 stmt2 in
        (gamma3, Sif(new_expr, new_stmt1, new_stmt2))
    | Ptree.Swhile(expr, stmt) ->
        let (gamma1, new_expr) = convert_expr gamma expr in
        let (gamma2, new_stmt) = convert_stmt gamma1 stmt in
        (gamma2, Swhile(new_expr, new_stmt))
    | Ptree.Sblock(block) ->
        let new_block = convert_block gamma block in
        (gamma, Sblock(new_block))
    | Ptree.Sreturn(expr) ->
        let (new_gamma, new_expr) = convert_expr gamma expr in
        (* TODO: check the type of return *)
        (new_gamma, Sreturn(new_expr))
and convert_expr (gamma: gamma_type) (expr: Ptree.expr) : gamma_type * expr =
    (* print_string "CONVERT EXPR"; *)
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

let fake_structure =
    {
        str_name = "structure_non_existent_for_recursive_purposes";
        str_fields = Hashtbl.create 0;
    }

let purify_structure structure =
    let aux ident field =
        match field.field_typ with
        | Tstructp(s) ->
            if s.str_name = "structure_non_existent_for_recursive_purposes" then
                Hashtbl.replace structure.str_fields ident {
                    field_name = field.field_name;
                    field_typ = Tstructp(structure);
                }
        | _ -> ()
    in
    Hashtbl.iter aux structure.str_fields

let execute_structure gamma ((ident, decl_var_list):Ptree.decl_struct) : structure  =
    let table = Hashtbl.create 17 in
    let rec aux (l: Ptree.decl_var list) =
        match l with
        | [] -> ()
        | (Ptree.Tint, small_ident)::q ->
            if Hashtbl.mem table (small_ident.id) then
                raise(Error("Twice the same name of field in structure"))
            else
                Hashtbl.add table small_ident.id {field_name = small_ident.id; field_typ = Tint}; aux q
        | (Ptree.Tstructp(other_ident), small_ident)::q ->
            if Hashtbl.mem table (small_ident.id) then
                raise(Error("Twice the same name of field in structure"))
            else
                let s =
                    if other_ident.id = (ident.id) then fake_structure
                    else get_structure gamma (other_ident.id)
                in Hashtbl.add table small_ident.id {field_name = small_ident.id; field_typ = Tstructp(s)}; aux q
    in aux decl_var_list;
    let s = {
        str_name = ident.id;
        str_fields = table;
    } in
    purify_structure s;
    s

let convert_function gamma0 (decl_fun: Ptree.decl_fun) : decl_fun =
    let typ = convert_typ gamma0 (decl_fun.fun_typ) in
    let gamma1 = set_ret_type gamma0 typ in
    let gamma2 = reset_env gamma1 in
    let name = (decl_fun.fun_name).id in
    let formals = convert_list gamma2 (decl_fun.fun_formals) in
    let gamma3 = add_to_env gamma2 formals in
    let fake_function = {
        fun_typ = typ;
        fun_name = name;
        fun_formals = formals;
        fun_body = ([], []);
    }
    in
    let gamma4 = add_fun gamma3 fake_function in
    let block = convert_block gamma4 (decl_fun.fun_body) in
    {
        fun_typ = typ;
        fun_name = name;
        fun_formals = formals;
        fun_body = block;
    }

let empty_gamma =
    let putchar = {
        fun_typ = Tint;
        fun_name = "putchar";
        fun_body = ([], []);
        fun_formals = [(Tint, "c")];
    } in
    let sbrk = {
        fun_typ = Tvoidstar;
        fun_name = "sbrk";
        fun_body = ([], []);
        fun_formals = [(Tint, "n")];
    } in

    {variables = []; structs = []; functions = [putchar; sbrk]; ret_typ = Tint}

let program file = 
    let rec aux gamma = function
    | [] -> gamma
    | Ptree.Dstruct(decl_struct)::q ->
        let structure = execute_structure gamma decl_struct in
        aux (add_structure gamma structure) q
    | Ptree.Dfun(decl_fun)::q ->
        let fonction = convert_function gamma decl_fun in
        aux (add_fun gamma fonction) q
    in {funs = (aux empty_gamma file).functions}
