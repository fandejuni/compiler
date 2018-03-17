open Format
open X86_64
open Ltltree

exception Error of string

let visited = Hashtbl.create 17
type instr = Code of X86_64.text | Label of Label.t
let code = ref []
let emit l i = code := Code i :: Label l :: !code
let emit_wl i = code := Code i :: !code
let emit_full x = code := x :: !code
let labels = Hashtbl.create 17
let need_label l = Hashtbl.add labels l ()

let register (r : Register.t) = match (r :> string) with
    | "%rax" -> X86_64.rax
    | "%rbx" -> X86_64.rbx
    | "%rcx" -> X86_64.rcx
    | "%rdx" -> X86_64.rdx
    | "%rsi" -> X86_64.rsi
    | "%rdi" -> X86_64.rdi
    | "%rbp" -> X86_64.rbp
    | "%rsp" -> X86_64.rsp
    | "%r8" -> X86_64.r8
    | "%r9" -> X86_64.r9
    | "%r10" -> X86_64.r10
    | "%r11" -> X86_64.r11
    | "%r12" -> X86_64.r12
    | "%r13" -> X86_64.r13
    | "%r14" -> X86_64.r14
    | "%r15" -> X86_64.r15
    | _ -> raise (Error "Unknown register")

let register_b (r : Register.t) = match (r :> string) with
    | "%rax" -> X86_64.al
    | "%rbx" -> X86_64.bl
    | "%rcx" -> X86_64.cl
    | "%rdx" -> X86_64.dl
    | "%rsi" -> X86_64.sil
    | "%rdi" -> X86_64.dil
    | "%rbp" -> X86_64.bpl
    | "%rsp" -> X86_64.spl
    | "%r8" -> X86_64.r8b
    | "%r9" -> X86_64.r9b
    | "%r10" -> X86_64.r10b
    | "%r11" -> X86_64.r11b
    | "%r12" -> X86_64.r12b
    | "%r13" -> X86_64.r13b
    | "%r14" -> X86_64.r14b
    | "%r15" -> X86_64.r15b
    | _ -> raise (Error "Unknown register")

let operand (op: Ltltree.operand) =
    match op with
    | Reg(r) -> reg (register(r))
    | Spilled(i) -> ind ~ofs:i X86_64.rbp 

let operand_b (op: Ltltree.operand) =
    match op with
    | Reg(r) -> reg (register_b(r))
    | Spilled(i) -> raise (Error "IMPOSSIBLE")

let convert_label (l: Label.t) = (l :> string)

let rec lin g l =
  if not (Hashtbl.mem visited l) then begin
    Hashtbl.add visited l ();
    instr g l (Label.M.find l g)
  end else begin
    need_label l;
    emit_wl (jmp (l :> string))
  end

and instr g l i =
    match i with
    | Ltltree.Econst (n, r, l1) ->
        begin emit l (movq (imm32 n) (operand r)); lin g l1 end
    | Ltltree.Eload(r1, i, r2, label) ->
        begin
            emit l (movq (ind ~ofs:i (register r1)) (operand (Reg(r2))));
            lin g label
        end
    | Ltltree.Estore(r1, r2, i, label) ->
        begin
            emit l (movq (operand (Reg(r1))) (ind ~ofs:i (register r2)));
            lin g label
        end
    | Ltltree.Egoto(label) ->
        begin
            if Hashtbl.mem visited label then
                emit_wl (jmp (convert_label label))
            else
                emit_full (Label(l));
                lin g label
        end
    | Ltltree.Ereturn -> emit l ret
    | Ltltree.Emunop(munop, r, label) ->
        begin
            begin match munop with
            | Maddi(n) -> emit l (addq (imm32 n) (operand r))
            | Msetei(n) ->
                begin
                    emit l (cmpq (imm32 n) (operand r));
                    emit_wl (sete (operand_b r))
                end
            | Msetnei(n) ->
                begin
                    emit l (cmpq (imm32 n) (operand r));
                    emit_wl (setne (operand_b r))
                end
            end
            ;
            lin g label
        end
    | Ltltree.Embinop(mbinop, r1, r2, label) ->
        begin
            let o1 = operand r1 in
            let o2 = operand r2 in
            begin match mbinop with
            | Mmov -> emit l (movq o1 o2)
            | Madd -> emit l (addq o1 o2)
            | Msub -> emit l (subq o1 o2)
            | Mmul -> emit l (imulq o1 o2)
            | Mdiv -> emit l (idivq o2)
            | Msete | Msetne | Msetl | Msetle | Msetg | Msetge ->
                begin 
                emit l (cmpq o1 o2);
                let b = operand_b r2 in
                match mbinop with
                | Msete -> emit_wl (sete  b)
                | Msetne -> emit_wl (setne b)
                | Msetl -> emit_wl (setl b)
                | Msetle -> emit_wl (setle b)
                | Msetg -> emit_wl (setg b)
                | Msetge -> emit_wl (setge b)
                | _ -> raise (Error "IMPOSSIBLE")
                end
            end
            ;
            lin g label
        end
    | Ltltree.Emubranch(mubranch, r, l1, l2) ->
        begin
            begin
            let lab = convert_label l1 in
            need_label l1;
            need_label l2;
            match mubranch with
            | Mjz ->
                begin
                    emit l (testq (operand r) (operand r));
                    emit_wl (jz lab);
                end
            | Mjnz ->
                begin
                    emit l (testq (operand r) (operand r));
                    emit_wl (jnz lab);
                end
            | Mjlei(n) -> 
                begin
                    emit l (testq (imm32 n) (operand r));
                    emit_wl (jle lab);
                end
            | Mjgi(n) -> 
                begin
                    emit l (testq (imm32 n) (operand r));
                    emit_wl (jg lab);
                end
            ;
            emit_wl (jmp (convert_label l2));
            lin g l2; lin g l1
            end
        end
    | Ltltree.Embbranch(mbbranch, r1, r2, l1, l2) ->
        begin
            begin
            emit l (cmpq (operand r1) (operand r2));
            need_label l1;
            need_label l2;
            match mbbranch with
            | Mjl -> emit_wl (jl (convert_label l1))
            | Mjle -> emit_wl (jle (convert_label l1))
            ;
            emit_wl (jmp (convert_label l2));
            lin g l2; lin g l1
            end
        end
    | Ltltree.Epush(r, label) ->
        begin
            emit l (pushq (operand r)); lin g label
        end
    | Ltltree.Ecall(ident, label) ->
        begin
            emit l (call ident); lin g label
        end
    | Ltltree.Epop(r, label) ->
        begin
            emit l (popq (register r)); lin g label
        end

let program (f: Ltltree.file) =
    let aux (deffun: Ltltree.deffun) =
        emit_wl (label (deffun.fun_name));
        lin (deffun.fun_body) (deffun.fun_entry)
    in
    List.iter aux (f.funs);
    code := List.rev !code;
    let text = ref (globl "main") in
    let treat_code = function
    | Code(c) -> text := (!text) ++ c
    | Label(l) ->
        if Hashtbl.mem labels l then text := (!text) ++ (label (convert_label l))
    in
    List.iter treat_code (!code);
    {
        text = !text;
        data = nop;
    }
