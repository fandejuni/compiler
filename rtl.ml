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
    | _ -> raise(Error("Unknown type of expression"))

let rec stmt (s: Ttree.stmt) destl retr exitl : instr =
    match s with
    | Ttree.Sreturn(old_e) -> expr old_e retr exitl
    | _ -> raise(Error("Unknown statement"))

let deffun (f: Ttree.decl_fun) exit_label : deffun =
    let r = Register.fresh () in
    let decl_var = (List.hd (snd (f.fun_body))) in
    let i = stmt decl_var exit_label r exit_label in
    let l_in = generate i in
    {
        fun_name = f.fun_name;
        fun_formals = []; (* TODO *)
        fun_result = r;
        fun_locals = Register.S.empty;
        fun_entry = l_in;
        fun_exit = exit_label;
        fun_body = !graph;
    }

let program (p: Ttree.file) : file =
    let exit_label = Label.fresh () in
    let f = List.hd (p.funs) in
    {
        funs = [deffun f exit_label]
    }

