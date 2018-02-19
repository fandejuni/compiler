open Ertltree

exception Error of string

let graph = ref Label.M.empty

let generate i =
    let l = Label.fresh () in
    graph := Label.M.add l i !graph;
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
  | Rtltree.Ecall(r, ident, r_list, l) -> raise(Error("ECALL"))

let program (file: Rtltree.file) = 
    raise (Error "Not done yet")
