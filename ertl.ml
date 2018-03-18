open Ertltree
open Format

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

let end_fun (deffun: Rtltree.deffun) regs =
    let l0 = generate Ereturn in
    let l1 = generate (Edelete_frame(l0)) in
    let rec aux label list_regs callee_saved =
    match (list_regs, callee_saved) with
    | ([], []) -> label
    | (r1::q1, r2::q2) ->
        let  l = generate (Embinop(Mmov, r1, r2, label)) in
        aux l q1 q2
    | _ -> raise (Error("Error in restoring callee saved registers"))
    in
    let l2 = aux l1 regs (Register.callee_saved) in
    add_graph deffun.fun_exit (Embinop(Mmov, deffun.fun_result, Register.rax, l2))


let begin_fun (deffun: Rtltree.deffun) lab =
    let rec get_args virtual_regs real_regs lab i =
    match (virtual_regs, real_regs) with
    | ([], _) -> lab
    | (vr::vq, []) -> let l = get_args vq [] lab (i-8) in
        generate (Eget_param(i, vr, l))
    | (vr::vq, rr::rq) -> let l = get_args vq rq lab i in
        generate (Embinop(Mmov, rr, vr, l))
    in
    let regs = ref [] in
    let rec aux label = function
    | [] -> label
    | t::q ->
        begin
            let r = Register.fresh () in
            regs := r::(!regs);
            let  l = generate (Embinop(Mmov, t, r, label)) in
            aux l q
        end
    in
    let n = max ((List.length deffun.fun_formals) - 6) 0 in
    let l0 = get_args (deffun.fun_formals) (Register.parameters) lab ((n + 1) * 8) in
    let l1 = aux l0 (List.rev Register.callee_saved) in
    (generate (Ealloc_frame(l1)), !regs)

let instr = function
  | Rtltree.Econst(r, n, l) -> Econst(r, n, l)
  | Rtltree.Eload(r1, p, r2, l)-> Eload(r1, p, r2, l)
  | Rtltree.Estore(r1, r2, p, l) -> Estore(r1, r2, p, l)
  | Rtltree.Emunop(m, r, l) -> Emunop(m, r, l)
  | Rtltree.Embinop(Mdiv, r1, r2, l) ->
          let (l3, _) = couple (Embinop(Mmov, Register.rax, r2, l)) in
          let (l2, _) = couple (Embinop(Mdiv, r1, Register.rax , l3)) in
          
          let (lpos, _) = couple (Econst(Int32.zero, Register.rdx , l2)) in
          
          let (lneg, _) = couple (Econst(Int32.of_int(-1), Register.rdx , l2)) 
          
          in
          let (l1, _) = couple (Emubranch(Mjgi(Int32.zero), Register.rdx ,lneg,lpos)) in
          Embinop(Mmov, r2, Register.rax, l1)
  | Rtltree.Embinop(m, r1, r2, l) -> Embinop(m, r1, r2, l)
  | Rtltree.Emubranch(mu, r, l1, l2) -> Emubranch(mu, r, l1, l2)
  | Rtltree.Embbranch(mb, r1, r2, l1, l2) -> Embbranch(mb, r1, r2, l1, l2)
  | Rtltree.Egoto(l) -> Egoto(l)
  | Rtltree.Ecall (r,fid,args,exitl) -> 
    begin 
      let nargs= min (List.length Register.parameters) (List.length args) in
      let rec load_param instr = function 
      |(_,[])-> instr
      |(paramr::q, reg::t) -> let l = (generate (load_param instr (q,t))) in 
        Embinop(Mmov,reg, paramr,l)
      |([],reg::t) -> 
            let l = (generate (load_param instr ([],t))) in Epush_param(reg,l)
      in 
      let n = (List.length args) - nargs in
      let l_depiler = generate (Emunop(Maddi(Int32.of_int (8*n)), Register.rsp, exitl)) in
      let l_mov_result = generate (Embinop(Mmov, Register.result, r, l_depiler)) in
      let i_ecall= ( Ecall(fid,nargs,l_mov_result)) in 
      load_param i_ecall (Register.parameters,args)
    end

let convert_cfg (f: Rtltree.deffun) =
    let aux label i =
        add_graph label (instr i)
    in
    let (label, regs) = begin_fun f (f.fun_entry) in
    end_fun f regs;
    Label.M.iter aux (f.fun_body);
    label

let deffun (f: Rtltree.deffun) =
    graph := Label.M.empty;
    let entry_lab = convert_cfg f in
    {
        fun_name = f.fun_name;
        fun_formals = min (List.length Register.parameters) (List.length f.fun_formals);
        fun_locals = f.fun_locals;
        fun_entry = entry_lab;
        fun_body = !graph;
    }

let program (file: Rtltree.file) = 
    {
        funs = List.map deffun file.funs;
    }
