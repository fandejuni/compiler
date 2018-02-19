open Ertltree

exception Error of string
exception Remaining_args of register list

let param_reg = List.length Register.parameters
let caller_saved = List.length Register.caller_saved
let callee_saved = List.length Register.callee_saved


let graph = ref Label.M.empty

let add_graph l i =
    graph := Label.M.add l i !graph

let generate i =
    let l = Label.fresh () in
    add_graph l i;
    l

let couple i =
    (generate i, i)

let instr = function
  | Rtltree.Econst(r, n, l) -> Econst(r, n, l)
  | Rtltree.Eload(r1, p, r2, l)-> Eload(r1, p, r2, l)
  | Rtltree.Estore(r1, r2, p, l) -> Estore(r1, r2, p, l)
  | Rtltree.Emunop(m, r, l) -> Emunop(m, r, l)
  | Rtltree.Embinop(Mdiv, r1, r2, l) ->
          let (l3, _) = couple (Embinop(Mmov, Register.rax, r2, l)) in
          let (l2, _) = couple (Embinop(Mdiv, r1, Register.rax, l3)) in
          Embinop(Mmov, r2, Register.rax, l2)
  | Rtltree.Embinop(m, r1, r2, l) -> Embinop(m, r1, r2, l)
  | Rtltree.Emubranch(mu, r, l1, l2) -> Emubranch(mu, r, l1, l2)
  | Rtltree.Embbranch(mb, r1, r2, l1, l2) -> Embbranch(mb, r1, r2, l1, l2)
  | Rtltree.Egoto(l) -> Egoto(l)
  | Rtltree.Ecall (r,fid,args,exitl) -> 
    begin 
      let nargs= min 6 (List.length args) in
      let rec load_param instr = function 
      |(_,[])-> instr
      |(paramr::q, reg::t) -> let l = (generate (load_param instr (q,t))) in 
        Embinop(Mmov,reg, paramr,l)
      |([],reg::t) -> 
            let l = (generate (load_param instr ([],t))) in Epush_param(reg,l)
      in 
      let n = (List.length args) - nargs in
      let l_depiler = generate (Emunop(Maddi(Int32.of_int (-n)), Register.rsp, exitl)) in
      let l_mov_result = generate (Embinop(Mmov, Register.result, r, l_depiler)) in
      let i_ecall= ( Ecall(fid,nargs,l_mov_result)) in 
      load_param i_ecall (Register.parameters,args)
    end

let convert_cfg cfg =
    let rec aux label i =
        add_graph label (instr i)
    in
    Label.M.iter aux cfg

let deffun (f: Rtltree.deffun) =
    graph := Label.M.empty;
    add_graph f.fun_exit Ereturn;
    convert_cfg f.fun_body;
    {
        fun_name = f.fun_name;
        fun_formals = min 6 (List.length f.fun_formals);
        fun_locals = f.fun_locals;
        fun_entry = f.fun_entry;
        fun_body = !graph;
    }

let program (file: Rtltree.file) = 
    {
        funs = List.map deffun file.funs;
    }
