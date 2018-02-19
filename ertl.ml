open Ertltree

exception Error of string
exception Remaining_args of register list

let param_reg = List.length Register.parameters
let caller_saved = List.length Register.caller_saved
let callee_saved = List.length Register.callee_saved

let save_ecall = function
    |Rtltree.Ecall (r,fid,args,exitl) -> 
        begin 
            let nargs= min(6,List.length args) in
            let rec load_param destl= function 
            |(_,[])-> destl
            |(paramr::q, reg::t) -> let l = (generate Embinop(Mmov,reg, paramr )) in 
                (load_param l q t)
            |([],rargs) -> raise( Remaining_args rargs)
        in try load_param exitl Register.parameters args with
        |Remaining_args(rargs) -> store_stack (rargs)
        end
    |_ -> raise (Error "pas une fonction a garder")

let program (file: Rtltree.file) = 
    raise (Error "Not done yet")
