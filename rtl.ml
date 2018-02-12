open Rtltree

exception Error of string

let graph = ref Label.M.empty

let generate i =
    let l = Label.fresh () in
    graph := Label.M.add l i !graph;
    l

let rec expr (e: Ttree.expr) destrl destl : instr =
    match e.expr_node with
    | Ttree.Econst(i) -> Econst(i, destrl, destl)
    | Ttree.Ebinop(binop, e1, e2) ->
        begin
            match binop with
            | Ptree.Badd ->
                let r1 = Register.fresh () in
                let i_op = Embinop(Madd, r1, destrl, destl) in
                let l_op = generate i_op in
                let i2 = expr e2 destrl l_op in
                let l2 = generate i2 in
                let i1 = expr e1 r1 l2 in
                i1
            | _ -> raise(Error("Unknown operation"))
        end
    | _ -> raise(Error("Unknown type of expression"))

let rec stmt (s: Ttree.stmt) destl retr exitl : instr =
    match s with
    | Ttree.Sreturn(old_e) -> expr old_e retr exitl
    | _ -> raise(Error("Unknown statement"))

let deffun (f: Ttree.decl_fun) exit_label : deffun =
    let list_args = List.map (fun x -> Register.fresh ()) (f.fun_formals) in
    let r = Register.fresh() in
    let current_label = ref exit_label in
    let treat_stmt (var_stmt: Ttree.stmt) : unit =
        let i = stmt var_stmt (!current_label) r exit_label in
        current_label := generate i
    in
    let stmt_reversed = List.rev (snd (f.fun_body)) in
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

