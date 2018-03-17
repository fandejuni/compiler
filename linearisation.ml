open Format
open X86_64
open Ltltree

exception Error of string

let visited = Hashtbl.create 17
type instr = Code of X86_64.text | Label of Label.t
let code = ref []
let emit l i = code := Code i :: Label l :: !code
let emit_wl i = code := Code i :: !code
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

let operand (op: Ltltree.operand) =
    match op with
    | Reg(r) -> reg (register(r))
    | Spilled(i) -> ind ~ofs:i X86_64.rbp 

let convert_label (l: Label.t) = (l :> string)

let rec lin g l =
  if not (Hashtbl.mem visited l) then begin
    Hashtbl.add visited l ();
    instr g l (Label.M.find l g)
  end else begin
    need_label l;
    emit_wl (jmp (l :> string))
  end

and instr g l = function
    | Ltltree.Econst (n, r, l1) ->
        emit l (movq (imm32 n) (operand r)); lin g l1
    | Ltltree.Eload(r1, i, r2, label) ->
        emit l (movq (ind ~ofs:i (register r1)) (operand (Reg(r2))));
        lin g label
    | Ltltree.Estore(r1, r2, i, label) ->
        emit l (movq (operand (Reg(r1))) (ind ~ofs:i (register r2)));
        lin g label
    | Ltltree.Egoto(label) ->
        emit l (jmp (convert_label label)); lin g label
    | Ltltree.Ereturn ->
        emit l ret
    | Ltltree.Emunop(munop, r, label) ->
        let i =
        begin match munop with
        | Maddi(n) -> addq (imm32 n) (operand r)
        | Msetei(n) -> raise (Error "TODO")
        | Msetnei(n) -> raise (Error "TODO")
        end in
        emit l i; lin g label
    | Ltltree.Embinop(mbinop, r1, r2, label) ->
        let o1 = operand r1 in
        let o2 = operand r2 in
        let i =
        begin match mbinop with
		| Mmov -> movq o1 o2
		| Madd -> addq o1 o2
		| Msub -> subq o1 o2
		| Mmul -> imulq o1 o2
		| Mdiv -> raise (Error "TODO")
		| Msete -> raise (Error "TODO")
		| Msetne -> raise (Error "TODO")
		| Msetl -> raise (Error "TODO")
		| Msetle -> raise (Error "TODO")
		| Msetg -> raise (Error "TODO")
		| Msetge -> raise (Error "TODO")
        end in
        emit l i; lin g label
    | Ltltree.Emubranch(mubranch, r, l1, l2) ->
        begin match mubranch with
        | Mjz ->
            begin
                emit l (jz (convert_label l1))
            end
		| Mjnz -> raise (Error "TODO")
		| Mjlei(n) -> raise (Error "TODO")
		| Mjgi(n) -> raise (Error "TODO")
        ;
        let l2 = Label.fresh () in
        emit l2 (jmp (convert_label l2));
        lin g l2; lin g l1;
        raise (Error "TODO")
		end
    | Ltltree.Embbranch(mbbranch, o1, o2, l1, l2) ->
		begin
        match mbbranch with
        | Mjl -> emit l (jl (convert_label l1))
		| Mjle -> emit l (jle (convert_label l1))
        ;
        let l2 = Label.fresh () in
        emit l2 (jmp (convert_label l2));
        lin g l2; lin g l1
        end
    | Ltltree.Epush(r, label) ->
        emit l (pushq (operand r)); lin g label
    | Ltltree.Ecall(ident, label) ->
        emit l (call ident); lin g label
    | Ltltree.Epop(r, label) ->
        emit l (popq (register r)); lin g label

let program (f: Ltltree.file) =
    let aux (deffun: Ltltree.deffun) =
        emit_wl (label (deffun.fun_name));
        lin (deffun.fun_body) (deffun.fun_entry)
    in
    List.iter aux (f.funs);
    let text = ref (globl "main") in
    let treat_code = function
    | Code(c) -> text := c ++ (!text)
    | Label(l) ->
        if Hashtbl.mem labels l then text := (label (convert_label l)) ++ (!text)
    in
    List.iter treat_code (!code);
    let p = {
        text = !text;
        data = nop;
    } in
    print_program std_formatter p
