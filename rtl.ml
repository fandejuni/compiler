open Rtltree

exception Error of string

let graph = ref Label.M.empty
let local_variables = ref (Hashtbl.create 17)
let current_locals = ref Register.S.empty

let generate i =
    let l = Label.fresh () in
    graph := Label.M.add l i !graph;
    l

let fresh_register () =
    let r = Register.fresh () in
    current_locals := Register.S.add r !current_locals;
    r

let couple e =
    (generate e, e)

let rec condition e truel falsel retr =
    let r = fresh_register () in
    let i_op = Emubranch(Mjz, r, falsel, truel) in 
    let l_op = generate i_op in 
    expr e r ?truel:(Some truel) l_op
and expr (e: Ttree.expr) destrl ?truel destl: instr =
    match e.expr_node with
    | Ttree.Econst(i) ->
        Econst(i, destrl, destl)
    | Ttree.Eaccess_local(ident) ->
        let r = Hashtbl.find (!local_variables) ident in
        Embinop(Mmov, r, destrl, destl)
    | Ttree.Eassign_local(ident, e) ->
        let r_left = Hashtbl.find (!local_variables) ident in
        let (l_assign, i_assign) = couple (Embinop(Mmov, destrl, r_left, destl)) in
        expr e destrl l_assign
    | Ttree.Ebinop(binop, e1, e2) -> let r1 = fresh_register () in 
        begin
            match binop with
            | Ptree.Beq | Ptree.Bneq | Ptree.Blt | Ptree.Ble | Ptree.Bgt | Ptree.Bge | Ptree.Badd | Ptree.Bsub | Ptree.Bmul | Ptree.Bdiv ->
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
                | _ -> raise(Error("This shouldn't happen"))
                in
                let l_op = generate i_op in
                let i2 = expr e1 destrl l_op in
                let l2 = generate i2 in
                let i1 = expr e2 r1 l2 in
                i1
            end
            | _ ->
                begin
                let truelabel = 
                match truel with
                | Some x -> x
                | _ -> raise(Error("No true branch specified (lazy)"))
                in
                match binop with
                | Ptree.Band ->
                    let (lab2, exp2) = couple (condition e2 truelabel destl destrl) in
                    condition e1 lab2 destl destrl
                | Ptree.Bor ->
                    let (lab2, exp2) = couple (condition e2 truelabel destl destrl) in
                    condition e1 truelabel lab2 destrl
                | _ -> raise(Error("This shouldn't happen"))
                end
        end
    | Ttree.Eunop(Unot,e1) -> let i_op = Emunop(Msetei(0l),destrl,destl) in
    let l_op = generate i_op in
    expr e1 destrl l_op
    | Ttree.Eunop(Uminus,e1) ->
        let r1 = fresh_register () in 
        let i_op = Embinop(Msub, r1, destrl, destl) in
        let l_op = generate i_op in
        let l2 = generate (Econst(0l,destrl, l_op)) in 
        let i1 = expr e1 r1 l2 in
            i1
    | Ttree.Ecall(ident, expl) ->
        let l = List.map (fun x -> (x, fresh_register ())) expl in
        let call = Ecall(destrl, ident, (List.map snd l), destl) in
        let l_call = generate call in
        let l2 = List.rev l in
        let current_label = ref l_call in
        let iter (old_e, r) =
            let e = expr old_e r !current_label in
            current_label := generate e;
        in
        List.iter iter l2;
        Label.M.find !current_label !graph
    | Ttree.Eaccess_field(e, f) -> 
    begin 
        let reg_e = fresh_register () in
        
        let i_load = match e.expr_typ with
        |Tstructp(s) -> let pos = (Hashtbl.find (s.str_fields) (f.field_name)).position in
            Eload(reg_e,pos,destrl,destl)
        |_ -> raise (Error "accessing a field of a non struct") 
        in
        let l_load = generate i_load in 
        expr e reg_e l_load
    end
    | Ttree.Eassign_field(_, _, _) -> raise(Error("Eassign_field"))
    | Ttree.Esizeof(s) -> let i = Int32.of_int (8 * Hashtbl.length (s.str_fields)) in
        Econst(i, destrl, destl)

let create_local_variable ((_, ident): Ttree.decl_var) r =
    Hashtbl.add (!local_variables) ident r

let generate_local_variables list_decl_var =
    List.map (fun x -> let r = fresh_register () in create_local_variable x r; r) list_decl_var

let rec generate_stmt r exit_label list_stmts =
    let current_label = ref exit_label in
    let treat_stmt (var_stmt: Ttree.stmt) : unit =
        let (lab, i) = stmt var_stmt (!current_label) r exit_label in
        current_label := lab
    in
    let stmt_reversed = List.rev list_stmts in
    List.iter treat_stmt stmt_reversed;
    !current_label
and stmt (s: Ttree.stmt) destl retr exitl : label * instr =
    match s with
    | Ttree.Sreturn(e) -> couple (expr e retr exitl)
    | Ttree.Sblock(list_decl_var, list_stmts) ->
        let _ = generate_local_variables list_decl_var in
        let current_label = generate_stmt retr destl list_stmts in
        (current_label, Label.M.find current_label !graph)
    | Ttree.Sskip -> couple (Egoto(destl))
    | Ttree.Sexpr(e) -> couple (expr e retr destl)
    | Ttree.Sif(e, s1, s2) -> 
        let (l1, _) = stmt s1 destl retr exitl in
        let (l2, _) = stmt s2 destl retr exitl in
        couple (condition e l1 l2 retr)
    | Ttree.Swhile(old_e, old_s) ->
        let end_loop_label = Label.fresh () in
        let (label_s, i_s) = stmt old_s end_loop_label retr exitl in
        let (label_e, e) = couple (condition old_e label_s destl retr) in
        let goto = Egoto(label_e) in
        graph := Label.M.add end_loop_label goto !graph;
        (label_e, e)

let deffun (f: Ttree.decl_fun) exit_label : deffun =
    Hashtbl.clear !local_variables;
    let (list_decl_var, list_stmts) = f.fun_body in
    let list_args = List.map (fun x -> let r = fresh_register () in create_local_variable x r; r) (f.fun_formals) in
    let r = Register.fresh() in
    let locals = generate_local_variables list_decl_var in
    current_locals := List.fold_left (fun s x -> Register.S.add x s) Register.S.empty locals;
    (* current_locals := List.fold_left (fun s x -> Register.S.add x s) !current_locals list_args;
    current_locals := Register.S.add r !current_locals; *)
    let current_label = generate_stmt r exit_label list_stmts in
   {
        fun_name = f.fun_name;
        fun_formals = list_args;
        fun_result = r;
        fun_locals = !current_locals;
        fun_entry = current_label;
        fun_exit = exit_label;
        fun_body = !graph;
    }

let program (p: Ttree.file) : file =
    let aux (decl_fun: Ttree.decl_fun) =
        let exit_label = Label.fresh () in
        deffun decl_fun exit_label
    in
    {
        funs = List.map aux (List.filter (fun (f:Ttree.decl_fun) -> f.fun_name <> "sbrk" && f.fun_name <> "putchar") (p.funs))
    }

