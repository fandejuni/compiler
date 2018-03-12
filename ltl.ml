open Format
open Ltltree

exception Error of string

type live_info = {
         instr: Ertltree.instr;
          succ: Label.t list;    (* successeurs *)
  mutable pred: Label.set;       (* prédécesseurs *)
          defs: Register.set;    (* définitions *)
          uses: Register.set;    (* utilisations *)
  mutable  ins: Register.set;    (* variables vivantes en entrée *)
  mutable outs: Register.set;    (* variables vivantes en sortie *)
}

type arcs = { prefs: Register.set; intfs: Register.set }
type igraph = arcs Register.map

type color = operand
type coloring = color Register.map

let graph = ref Label.M.empty

let add_graph l i =
    graph := Label.M.add l i !graph

let generate i =
    let l = Label.fresh () in
    add_graph l i;
    l

let fill_pred (m: live_info Label.map) =
    let fill label x =
        List.iter (fun l -> let y = Label.M.find l m in y.pred <- Label.S.add label y.pred) x.succ
    in
    Label.M.iter fill m

let pop s =
    let x = List.hd (Label.S.elements (!s)) in
    s := Label.S.remove x (!s);
    x

let print_set = Register.print_set

let spillify n =
    (n+1) * (-8)

let kildall m =
    let get l =
        Label.M.find l m
    in
    let s = ref Label.S.empty in
    Label.M.iter (fun x _ -> s := Label.S.add x !s) m;
    let rec iterer () =
        if not (Label.S.is_empty !s) then
            begin
                let l = pop s in
                let x = get l in
                let outs = match x.succ with
                | [] -> Register.S.empty
                | [x] -> let y = get x in y.ins
                | [a; b] -> let c = get a in let d = get b in Register.S.union c.ins d.ins
                | _ -> raise (Error("Too many successors"))
                in
                x.outs <- outs;
                let old_in = x.ins in
                x.ins <- Register.S.union x.uses (Register.S.diff x.outs x.defs);
                if not (x.ins = old_in) then
                    begin
                        let rec add l =
                            s := Label.S.add l !s
                        in
                        List.iter add (Label.S.elements x.pred)
                    end
                ;
                iterer ()
            end
    in
    iterer ()

let convert_rsp = function
    | Ertltree.Emunop(Maddi(_), r, l) when r = Register.rsp -> Ertltree.Egoto(l)
    | i -> i

let liveness (cfg: Ertltree.cfg) =
    let aux instr =
        begin
            let (defs, uses) = Ertltree.def_use instr in
            let s_defs = ref Register.S.empty in
            let s_uses = ref Register.S.empty in
            List.iter (fun x -> s_defs := Register.S.add x !s_defs) defs;
            List.iter (fun x -> s_uses := Register.S.add x !s_uses) uses;
            {
                instr = instr;
                succ = Ertltree.succ instr;
                pred = Label.S.empty;
                defs = !s_defs;
                uses = !s_uses;
                ins = Register.S.empty;
                outs = Register.S.empty;
            }
        end
    in
    let m = Label.M.map aux (Label.M.map convert_rsp cfg) in
    fill_pred m;
    kildall m;
    m

let make m : igraph =
    let g = ref Register.M.empty in
    let add_pref_to_arc arc r =
        {
            intfs = arc.intfs;
            prefs = Register.S.add r arc.prefs;
        }
    in
    let add_interf_to_arc arc r =
        {
            intfs = Register.S.add r arc.intfs;
            prefs = Register.S.remove r arc.prefs;
        }
    in
    let get_element r =
        if not (Register.M.exists (fun k _ -> r = k) !g) then
            g := Register.M.add r {prefs = Register.S.empty; intfs = Register.S.empty} !g;
        Register.M.find r !g;
    in
    let add_to_graph f r1 r2 =
        if r1 <> r2 then
            begin
                let a1 = get_element r1 in
                let a2 = get_element r2 in
                g := Register.M.add r1 (f a1 r2) !g;
                g := Register.M.add r2 (f a2 r1) !g;
            end
    in
    let add_pref _ live =
        match live.instr with
        | Embinop(Mmov, r1, r2, _) when r1 <> r2 ->
            add_to_graph add_pref_to_arc r1 r2
        | _ -> ()
    in
    let add_interf _ live =
        let set_v = live.defs in
        let set_w = ref live.outs in
        begin
            match live.instr with
            | Embinop(Mmov, w, v, _) when w = v -> set_w := Register.S.empty
            | Embinop(Mmov, w, v, _) -> set_w := Register.S.remove w !set_w
            | _ -> ()
        end
        ;
        Register.S.iter (fun v -> Register.S.iter (add_to_graph add_interf_to_arc v) !set_w) set_v;
    in
    Label.M.iter add_pref m;
    Label.M.iter add_interf m;
    !g
    
let choose_register_to_spill g (todo: Register.set Register.map) (coloring: coloring) =
    let (x, _) = Register.M.choose todo in
    x
let map_keys_to_set m =
    let s= ref Register.S.empty in
    let aux v _ = s:= Register.S.add v !s 
    in Register.M.iter aux m;
    !s

let choose_register_to_color g (todo: Register.set Register.map) (coloring: coloring) =
    let score = ref 0 in 
    let ret = ref None in 
    let max_priority r possible_colors = 
        let arcs= Register.M.find r g in 
        let colored = map_keys_to_set coloring in
        let colored_prefs = Register.S.inter possible_colors (Register.S.inter arcs.prefs colored) in 
        let has_colored_prefs = not (Register.S.is_empty colored_prefs) in 
        let prio_score = match (Register.S.cardinal possible_colors) with
            |1 -> begin
                if has_colored_prefs then
                    4 
                else 3
            end
            |0 -> -1
            |_ -> begin 
                if has_colored_prefs then
                    2
                else 1
            end
        in
        if prio_score > !score then
            begin
                score := prio_score;
                if has_colored_prefs then begin
                    let col = Register.M.find (Register.S.choose colored_prefs) coloring in 
                ret:= Some (r,col) end
                else 
                    let col = Reg (Register.S.choose possible_colors) in
                    ret:= Some (r,col)
            end
    in
    Register.M.iter max_priority todo;
    !ret

let print_color fmt = function
  | Reg hr    -> fprintf fmt "%a" Register.print hr
  | Spilled n -> fprintf fmt "stack %d" (-8*(n+1))

let print_coloring cm =
    let aux r cr =
        if not (Register.S.mem r Register.allocatable) then
            printf "%a -> %a@\n" Register.print r print_color cr
    in
    print_string "\n\n=== COLORING =============================================\n\n";
    Register.M.iter aux cm

let print_todo todo =
    let aux r s = Register.print std_formatter r;
    print_string " -> ";
    print_set std_formatter s;
    print_string " \n";
    in Register.M.iter aux !todo

let color real_g : coloring * int =
    let g = ref real_g in
    let todo = ref Register.M.empty in
    let init r arcs =
        todo := Register.M.add r (Register.S.diff Register.allocatable arcs.intfs) !todo
    in
    Register.M.iter init !g;
    let coloring : coloring ref = ref Register.M.empty in
    let colorer r colour =
        todo := Register.M.remove r !todo;
        coloring := Register.M.add r colour !coloring;
        match colour with
        | Reg(c) ->
            begin
                let remove_color r =
                    begin
                        (*
                        print_string "\nRemove color: ";
                        Register.print std_formatter c;
                        print_string " from ";
                        Register.print std_formatter r;
                        *)
                        try (
                            let s = Register.M.find r !todo in
                            todo := Register.M.add r (Register.S.remove c s) !todo;
                            (*print_string "Effectif!";
                            Register.print_set std_formatter (Register.S.remove c s);*)
                            )
                        with 
                            |Not_found -> ();
                    end
                in
                let arcs = Register.M.find r !g in
                Register.S.iter remove_color arcs.intfs
            end
        | _ -> ()
    in
    let physical_register r _ =
        if Register.S.mem r Register.allocatable then
            colorer r (Reg(r))
    in
    Register.M.iter physical_register !g;
    let i = ref 0 in
    let rec aux () =
        if not (Register.M.is_empty !todo) then
            begin
                begin
                match choose_register_to_color !g !todo !coloring with
                | Some (r, c) -> colorer r c
                | None ->
                    begin
                        let r = choose_register_to_spill g !todo !coloring in
                        coloring := Register.M.add r (Spilled(spillify !i)) !coloring;
                        todo := Register.M.remove r !todo;
                        i := !i + 1
                    end
                end;
                aux ()
            end
    in
    aux ();
    (!coloring, !i)

let convert_ltl (coloring, i) deffun =
    graph := Label.M.empty;
    let get r =
        if r = Register.rsp then
            Reg(Register.rsp)
        else
            Register.M.find r coloring
    in
    let load n o1 o2 l = match (o1, o2) with
        | (Reg(r1), Reg(r2)) -> Eload(r1, n, r2, l)
        | (Reg(r1), Spilled(n2)) ->
            let l2 =  generate (Estore(Register.tmp1, Register.rbp, n2, l)) in
            Eload(r1, n, Register.tmp1, l2)
        | (Spilled(n1), Reg(r2)) ->
            let l2 = generate (Eload(Register.tmp1, n, r2, l)) in
            Eload(Register.rbp, n1, Register.tmp1, l2)
        | (Spilled(n1), Spilled(n2)) ->
            let l3 = generate (Estore(Register.tmp2, Register.rbp, n2, l)) in
            let l2 = generate (Eload(Register.tmp1, n, Register.tmp2, l3)) in
            Eload(Register.rbp, n1, Register.tmp1, l2)
    in
    let store o1 n o2 l = match (o1, o2) with
        | (Reg(r1), Reg(r2)) -> Estore(r1, r2, n, l)
        | (Reg(r1), Spilled(n2)) ->
            let l2 = generate (Estore(r1, Register.tmp1, n, l)) in
            Eload(Register.rbp, n2, Register.tmp1, l2)
        | (Spilled(n1), Reg(r2)) ->
            let l2 = generate (Estore(Register.tmp1, r2, n, l)) in
            Eload(Register.rbp, n1, Register.tmp1, l2)
        | (Spilled(n1), Spilled(n2)) ->
            let l3 = generate (Estore(Register.tmp1, Register.tmp2, n, l)) in
            let l2 = generate (Eload(Register.rbp, n1, Register.tmp1, l3)) in
            Eload(Register.rbp, n2, Register.tmp2, l2)
    in
    let aux l instr = 
        let i = match instr with
        | Ertltree.Econst(i32, register, label) -> Econst(i32, get register, label)
        | Ertltree.Eload(r1, i, r2, label) -> load i (get r1) (get r2) label
        | Ertltree.Estore(r1, r2, i, label) -> store (get r1) i (get r2) label
        | Ertltree.Emunop(munop, register, label) -> Emunop(munop, get register, label)
        | Ertltree.Embinop(Mmov, r1, r2, label) when (get r1) = (get r2) -> Egoto(label)
        | Ertltree.Embinop(mbinop, r1, r2, label) -> Embinop(mbinop, get r1, get r2, label)
        | Ertltree.Emubranch(mubranch, register, l1, l2) -> Emubranch(mubranch, get register, l1, l2)
        | Ertltree.Embbranch(mbbranch, r1, r2, l1, l2) -> Embbranch(mbbranch, get r1, get r2, l1, l2)
        | Ertltree.Egoto(label) -> Egoto(label)
        | Ertltree.Ecall(ident, i, label) -> Ecall(ident, label)
        | Ertltree.Ealloc_frame(label) ->
            let l3 = generate (Emunop(Maddi(Int32.of_int(-8 * i)), Reg(Register.rsp), label)) in
            let l2 = generate (Embinop(Mmov, Reg(Register.rsp), Reg(Register.rbp), l3)) in
            Epush(Reg(Register.rbp), l2)
        | Ertltree.Edelete_frame(label) ->
            let l2 = generate (Epop(Register.rbp, label)) in
            Embinop(Mmov, Reg(Register.rbp), Reg(Register.rsp), l2)
        | Ertltree.Eget_param(i, register, label) ->
            Embinop(Mmov, Spilled(i), get register, label)
                (* load (i) (Reg(Register.rbp)) (get register) label *)
        | Ertltree.Epush_param(register, label) -> Epush(get register, label)
        | Ertltree.Ereturn -> Ereturn
        in
        add_graph l i
    in
    Label.M.iter aux deffun

let print_graph live fmt =
    let aux l i =
        begin
            let li = Label.M.find l live in
            fprintf fmt "%a: %a || d={%a} u={%a} i={%a} o={%a} \n"
                Label.print l Ertltree.print_instr i
                print_set li.defs print_set li.uses print_set li.ins print_set li.outs
        end
    in
    Ertltree.visit aux

let print_igraph ig =
  Register.M.iter (fun r arcs ->
    Format.printf "%s: prefs=@[%a@] intfs=@[%a@]@." (r :> string)
      Register.print_set arcs.prefs Register.print_set arcs.intfs) ig

let convert_deffun (f: Ertltree.deffun) =
  let m = liveness f.fun_body in
  let g = make m in
  (* print_igraph g; *)
  let (c, i) = color g in
  (* print_coloring c; *)
  convert_ltl (c, i) f.fun_body;
  {
      fun_name = f.fun_name;
      fun_body = !graph;
      fun_entry = f.fun_entry;
  }

let print_deffun fmt (f: Ertltree.deffun) = 
  fprintf fmt "%s(%d)@\n" f.fun_name f.fun_formals;
  fprintf fmt "  @[";
  fprintf fmt "entry : %a@\n" Label.print f.fun_entry;
  fprintf fmt "locals: @[%a@]@\n" Register.print_set f.fun_locals;
  let m = liveness f.fun_body in
  print_graph m fmt f.fun_body f.fun_entry;
  let g = make m in
  print_igraph g;
  let (c, i) = color g in
  print_coloring c;
  convert_ltl (c, i) f.fun_body;
  let ltl = {
      fun_name = f.fun_name;
      fun_body = !graph;
      fun_entry = f.fun_entry;
  }
  in
  print_deffun fmt ltl;
  fprintf fmt "@]@."

let print_file fmt (p: Ertltree.file) =
  fprintf fmt "=== ERTL =================================================@\n";
  List.iter (print_deffun fmt) p.funs

let program (p: Ertltree.file) =
    {
        funs = List.map convert_deffun p.funs;
    }
