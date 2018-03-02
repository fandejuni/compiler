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

let print_deffun fmt (f: Ertltree.deffun) = 
  fprintf fmt "%s(%d)@\n" f.fun_name f.fun_formals;
  fprintf fmt "  @[";
  fprintf fmt "entry : %a@\n" Label.print f.fun_entry;
  fprintf fmt "locals: @[%a@]@\n" Register.print_set f.fun_locals;
  print_graph (liveness f.fun_body) fmt f.fun_body f.fun_entry;
  fprintf fmt "@]@."

let print_file fmt (p: Ertltree.file) =
  fprintf fmt "=== ERTL =================================================@\n";
  List.iter (print_deffun fmt) p.funs

