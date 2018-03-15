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

let convert_label (l: Label.t) =
    match (l :> string) with
    | x -> x

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
    | Ltltree.Eload(r1, i, r2, label) -> raise (Error "TODO")
    | Ltltree.Estore(r1, r2, i, label) -> raise (Error "TODO")
    | Ltltree.Egoto(label) ->
            emit l (jmp (convert_label label)); lin g label
    | Ltltree.Ereturn ->
            emit l ret
    | Ltltree.Emunop(munop, operand, label) -> raise (Error "TODO")
    | Ltltree.Embinop(mbinop, o1, o2, label) -> raise (Error "TODO")
    | Ltltree.Emubranch(mubranch, operand, l1, l2) -> raise (Error "TODO")
    | Ltltree.Embbranch(mbbranch, o1, o2, l1, l2) -> raise (Error "TODO")
    | Ltltree.Epush(operand, label) -> raise (Error "TODO")
    | Ltltree.Ecall(ident, label) -> raise (Error "TODO")
    | Ltltree.Epop(register, label) -> raise (Error "TODO")

let program (f: Ltltree.file) =
    raise (Error "Not yet implemented")
