open Rtltree

exception Error of string

let graph = ref Label.M.empty
let local_variables = ref (Hashtbl.create 0)

let generate i =
    let l = Label.fresh () in
    graph := Label.M.add l i !graph;
    l

let rec expr (e: Ttree.expr) destrl destl : instr =
    match e.expr_node with
    | Ttree.Econst(i) -> Econst(i, destrl, destl)
    | Ttree.Eaccess_local(ident) ->
        let r = Hashtbl.find (!local_variables) ident in
        Eload(r, 0, destrl, destl)
    | Ttree.Eassign_local(ident, e) ->
        let r_left = Hashtbl.find (!local_variables) ident in
        let r_right = Register.fresh () in
        let i_assign = Estore(r_right, r_left, 0, destl) in
        let l_assign = generate i_assign in
        expr e r_right l_assign
    | Ttree.Ebinop(binop, e1, e2) -> let r1 = Register.fresh () in 
        begin
            let i_op = 
            match binop with
            | Ptree.Beq -> Embinop(Msete, r1, destrl, destl)
            | Ptree.Bneq-> Embinop(Msetne, r1, destrl, destl)
            | Ptree.Blt -> Embinop(Msetl, r1, destrl, destl)
            | Ptree.Ble -> Embinop(Msetle, r1, destrl, destl)
            | Ptree.Bgt -> Embinop(Msetg, r1, destrl, destl)
            | Ptree.Bge -> Embinop(Msetge, r1, destrl, destl)
            | Ptree.Badd -> Embinop(Madd, r1, destrl, destl)
            | Ptree.Bsub -> Embinop(Msub, r1, destrl, destl)
            | Ptree.Bmul -> Embinop(Mmul, r1, destrl, destl)
            | Ptree.Bdiv -> Embinop(Mdiv, r1, destrl, destl)
            | _ -> raise(Error("Unknown operation"))
            in
            let l_op = generate i_op in
            let i2 = expr e1 destrl l_op in
            let l2 = generate i2 in
            let i1 = expr e2 r1 l2 in
            i1
        end
    | Ttree.Eunop(Unot,e1) -> let i_op = Emunop(Msetei(0l),destrl,destl) in
    let l_op = generate i_op in
    expr e1 destrl l_op    
    | Ttree.Eunop(Uminus,e1) ->
        let r1 = Register.fresh () in 
        let i_op = Embinop(Msub, r1, destrl, destl) in
        let l_op = generate i_op in
        let l2 = generate (Econst(0l,destrl, l_op)) in 
        let i1 = expr e1 r1 l2 in
            i1
    | _ -> raise(Error("Unknown type of expression"))

let rec stmt (s: Ttree.stmt) destl retr exitl : instr =
    match s with
    | Ttree.Sreturn(e) -> expr e retr exitl
    | Ttree.Sblock(block) -> raise(Error("Block"))
    | Ttree.Sskip -> Egoto(destl)
    | Ttree.Sexpr(e) -> expr e retr destl
    | Ttree.Sif(e, s1, s2) -> raise(Error("Sif"))
    | Ttree.Swhile(old_e, old_s) ->
        let end_loop_label = Label.fresh () in
        let i_s = stmt old_s end_loop_label retr exitl in
        let label_s = generate i_s in
        let r = Register.fresh () in
        let i_expr = expr old_e r label_s in
        let label_expr = generate i_expr in
        

let deffun (f: Ttree.decl_fun) exit_label : deffun =
    local_variables := Hashtbl.create 17;
    let (list_decl_var, list_stmts) = f.fun_body in
    let list_args = List.map (fun x -> Register.fresh ()) (f.fun_formals) in (* TODO *)
    let r = Register.fresh() in
    let create_local_variable ((_, ident): Ttree.decl_var) =
        Hashtbl.add (!local_variables) ident (Register.fresh ())
    in
    List.iter create_local_variable list_decl_var;
    let current_label = ref exit_label in
    let treat_stmt (var_stmt: Ttree.stmt) : unit =
        let i = stmt var_stmt (!current_label) r exit_label in
        current_label := generate i
    in
    let stmt_reversed = List.rev list_stmts in
    List.iter treat_stmt stmt_reversed;
    {
        fun_name = f.fun_name;
        fun_formals = list_args;
        fun_result = r;
        fun_locals = Register.S.empty;
        fun_entry = !current_label;
        fun_exit = exit_label;
        fun_body = !graph;
    }

let program (p: Ttree.file) : file =
    let aux (decl_fun: Ttree.decl_fun) =
        let exit_label = Label.fresh () in
        deffun decl_fun exit_label
    in
    {
        funs = List.map aux (p.funs)
    }

