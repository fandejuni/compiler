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

let gamma_structure_find x (gamma: gamma_type) =
   let rec aux (l: Ptree.decl_struct list) =
    match l with
    | [] -> raise (Error "not an existing structure")
    | (name, dec_varl)::q -> if (name.id = x ) then dec_varl else (aux q)
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

let rec convert_type gamma (typ: Ptree.typ) : Ttree.typ =
    let rec fill struc = function
        |[] -> ()
        |((typ:Ptree.typ) , (ident:Ptree.ident))::q -> begin
            Hashtbl.add (struc.str_fields) ident.id {field_name = ident.id; field_typ = (convert_type gamma typ)};
            fill struc q
        end
    in match typ with 
    |Tint -> Tint
    |Tstructp ident -> begin 
        let struc = {
            str_name = ident.id;
            str_fields = Hashtbl.create 17
        } in fill struc (gamma_structure_find ident.id gamma); Tstructp struc
    end

let rec get_type_env id = function
    |[] -> raise (Error "get_type failed")
    |(typ, ident)::q when (id=ident) -> typ
    | _::q -> get_type_env id q

let rec find_function (ident: Ptree.ident) gamma =
    let rec aux (l: Ptree.decl_fun list) =
    match l with
    | [] -> raise(Error("This function doesn't exist"))
    | t::q -> if t.fun_name.id = ident.id then t else aux q
    in
    aux gamma.functions

let rec check_function gamma env (f: Ptree.decl_fun) l =
    (* TODO *)
    let rec aux (l_args: Ptree.decl_var list) l_exps =
    match (l_args, l_exps) with
    | ([], []) -> true
    | ((typ1, ident1)::q, exp::t) -> let typ = get_type_expr gamma env exp in (typ = (convert_type gamma typ1)) && aux q t
    | _ -> false
    in
    aux f.fun_formals l
and get_type_expr gamma env (exp : Ptree.expr) = 
    (* TODO *)
    match exp.expr_node with
    | Econst(0l) -> Ttypenull
    | Econst(i) -> Tint
    | Eright (lvalue)-> begin
        match lvalue with 
        |Lident(id) -> convert_type gamma (get_type_env id env)
        |Larrow (exp1, id) -> begin 
            match get_type_expr gamma env exp1 with
            |Tstructp(ident) -> convert_type gamma (get_type_env id (gamma_structure_find ident.str_name gamma))
            |_ -> raise (Error "assignement of a non structure")
        end
    end
    | Eassign (lvalue,exp1)-> if ((get_type_expr gamma env {expr_node = Eright(lvalue); expr_loc= exp.expr_loc}) = (get_type_expr gamma env exp1)) then (get_type_expr gamma env exp1) else raise (Error "assignment types not matching"); 
    | Eunop (unop,exp1) -> let t = get_type_expr gamma env exp1 in if t == Tint then Tint else raise(Error("Bad type expression for UNOP"))
    | Ebinop (binop, exp1 ,exp2) ->
        begin
            let t1 = get_type_expr gamma env exp1 in
            let t2 = get_type_expr gamma env exp2 in
            match binop with
            | Beq | Bneq ->
                if t1 = t2 || ((t1 = Ttypenull || t1 = Tint) && (t2 = Ttypenull || t2 = Tint))
                then Tint
                else raise(Error("Error with = or !="))
            | _ -> if ((t1 = Ttypenull || t1 = Tint) && (t2 = Ttypenull || t2 = Tint)) then Tint else raise(Error("Error with = or !="))
        end
    | Esizeof (ident) -> if gamma_structure_mem (ident.id) gamma then Tint else raise(Error("Size of not a structure"))
    | Ecall (ident,expl)-> let f = find_function ident gamma in
    if check_function gamma env f expl then (convert_type gamma f.fun_typ) else raise(Error("error in arguments of function"))

let rec check_statement gamma env (stmt: Ptree.stmt) ret_type =
    match stmt.stmt_node with
	| Ptree.Sskip -> true
    | Ptree.Sexpr(exp) -> ignore(get_type_expr gamma env exp); true
	| Ptree.Sif (exp, stmt1, stmt2) -> (get_type_expr gamma env exp = Tint) && (check_statement gamma env stmt1 ret_type) && (check_statement gamma env stmt2 ret_type)
	| Ptree.Swhile (exp,stmt1) -> (get_type_expr gamma env exp = Tint) && (check_statement gamma env stmt1 ret_type)
	| Ptree.Sblock (bloc)-> check_body gamma env bloc ret_type
	| Ptree.Sreturn (exp) -> get_type_expr gamma env exp = ret_type
and check_statements gamma env ret_type = function
    | [] -> true
    | t::q -> (check_statement gamma env t ret_type && check_statements gamma env ret_type q)
and check_body gamma env (vars, stmts) (ret_type: Ttree.typ) =
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
    let b3 = check_body gamma_prime decl_fun.fun_formals decl_fun.fun_body (convert_type gamma decl_fun.fun_typ) in
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

let convert_expr gamma expr : Ttree.expr =
    raise(Error("Not cool"))

let convert gamma p =
    let rec convert_stmt_node = function
		| Ptree.Sskip -> Sskip
        | Ptree.Sexpr(expr) -> Sexpr(convert_expr gamma expr)
		| Ptree.Sif(expr, stmt1, stmt2) -> Sif(
            convert_expr gamma expr,
            convert_stmt stmt1,
            convert_stmt stmt2)
		| Ptree.Swhile(expr, stmt) -> Swhile(
            convert_expr gamma expr,
            convert_stmt stmt)
		| Ptree.Sblock(block) -> Sblock(convert_block block)
		| Ptree.Sreturn(expr) -> Sreturn(convert_expr gamma expr)
    and convert_stmt (stmt: Ptree.stmt) =
        convert_stmt_node stmt.stmt_node
    and convert_var ((typ, ident): Ptree.decl_var) =
        (convert_type gamma typ, ident.id)
    and convert_block ((decl_var_list, stmt_list): Ptree.block) =
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
    in {funs = convert (aux gamma_vide p) p}
