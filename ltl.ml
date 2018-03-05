open Format

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

type color = Ltltree.operand
type coloring = color Register.map

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

let liveness (cfg: Ertltree.cfg) =
    let aux instr =
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
    in
    let m = Label.M.map aux cfg in
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

let choose_register_to_color g (todo: Register.set Register.map) (coloring: coloring) =
    None

let color g : coloring * int =
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
        | Ltltree.Reg(c) ->
            begin
                let remove_color r =
                    let s = Register.M.find r !todo in
                    todo := Register.M.add r (Register.S.remove c s) !todo;
                in
                let arcs = Register.M.find r !g in
                Register.S.iter remove_color arcs.intfs
            end
        | _ -> ()
    in
    let physical_register r _ =
        if Register.S.mem r Register.allocatable then
            colorer r (Ltltree.Reg(r))
    in
    Register.M.iter physical_register !g;
    let i = ref 0 in
    let rec aux () =
        if not (Register.M.is_empty !todo) then
            begin
                match choose_register_to_color g !todo !coloring with
                | Some (r, c) -> colorer r c
                | None ->
                    begin
                        let r = choose_register_to_spill g !todo !coloring in
                        coloring := Register.M.add r (Ltltree.Spilled(!i)) !coloring;
                        todo := Register.M.remove r !todo;
                        i := !i + 1
                    end
                ;
                aux ()
            end
    in
    aux ();
    (!coloring, !i)

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

let print ig =
  Register.M.iter (fun r arcs ->
    Format.printf "%s: prefs=@[%a@] intfs=@[%a@]@." (r :> string)
      Register.print_set arcs.prefs Register.print_set arcs.intfs) ig

let print_deffun fmt (f: Ertltree.deffun) = 
  fprintf fmt "%s(%d)@\n" f.fun_name f.fun_formals;
  fprintf fmt "  @[";
  fprintf fmt "entry : %a@\n" Label.print f.fun_entry;
  fprintf fmt "locals: @[%a@]@\n" Register.print_set f.fun_locals;
  let m = liveness f.fun_body in
  print_graph m fmt f.fun_body f.fun_entry;
  print (make m);
  fprintf fmt "@]@."

let print_file fmt (p: Ertltree.file) =
  fprintf fmt "=== ERTL =================================================@\n";
  List.iter (print_deffun fmt) p.funs

