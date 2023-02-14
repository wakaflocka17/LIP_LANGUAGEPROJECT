open Ast
open Types

let parse (s : string) : program =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog Lexer.read lexbuf in
  ast
;;

(******************************************************************************)
(*                      Small-step semantics of commands                      *)
(******************************************************************************)

exception NoRulesApplies

(* Environment undefined everywhere *)
let botenv = fun x -> raise (UnboundVar x)

(* Memory undefined everywhere *)
let botmem = fun l -> raise (UnboundLoc l)

(* Function that binds a value v to a parameter x for a function f*)
let bind f x v = fun x' -> if x'=x then v else f x'

(* Auxiliary function that returns the state after evaluating delarations of variables*)
let rec sem_decl_dv (e,l) = function
    Nullvar -> (e,l)
  | Var_decl(x) ->  let e' = bind e x (IVar l) in (e',l+1)
  | Array_decl(a, dim) -> let e' = bind e a (IArr (l, dim)) in (e', l+dim)
  | Seq_dv(dv1, dv2) -> 
      let (e', l') = sem_decl_dv (e, l) dv1 in sem_decl_dv (e', l') dv2

(* Auxiliary function that returns the state after evaluating delarations of procedures*)
let rec sem_decl_dp e = function
    | Nullproc -> e
    | Proc_decl(f, pf, c) -> let e' = bind e f (IProc(pf, c)) in e'
    | Seq_dp(dp1, dp2) -> 
      let e' = sem_decl_dp e dp1 in sem_decl_dp e' dp2

(* Function that returns the value stored in memory for a variable x, if it exists *)
let apply st x = match topenv st x with
   IVar l -> getmem st l
  | _ -> raise (TypeError "apply error")

(* Function that returns the value stored in memory for a cell at index i of an array a, if it exists *)
let apply_arr st a i = match topenv st a with
  | IArr(l, dim) when i < dim -> getmem st (l+i)
  | IArr(_, dim) -> raise (OOB("OOB: trying to access array " ^ a ^ " with dim " ^ string_of_int dim ^ " with index " ^ string_of_int i))
  | _ -> raise (TypeError "apply_arr error")

(* Function that copies in memory the content of an array with dimension dim that start at location l_start into a location l_target*)
let rec copy_array m l_start l_target dim =
  if dim > 0 then
    try
      match m l_start with
        | n -> copy_array (bind m l_target n) (l_start + 1) (l_target + 1) (dim - 1)
    
    with _ -> copy_array m (l_start + 1) (l_target + 1) (dim - 1)

  else m
    
(* Function that execute 1 step of the small-step semantic for expressions *)
let rec trace1_expr st = function
  | Var x -> (Const(apply st x), st)
  | Array(a, Const(i)) -> (Const(apply_arr st a i), st)
  | Array(a ,e) -> let (e', st') = trace1_expr st e in (Array(a, e'), st')
  | Not(True) -> (False,st)
  | Not(False) -> (True,st)
  | Not(e) -> let (e',st') = trace1_expr st e in (Not(e'),st')
  | And(True,e) -> (e,st)
  | And(False,_) -> (False,st)
  | And(e1,e2) -> let (e1',st') = trace1_expr st e1 in (And(e1',e2),st')
  | Or(True,_) -> (True,st)
  | Or(False,e) -> (e,st)
  | Or(e1,e2) -> let (e1',st') = trace1_expr st e1 in (Or(e1',e2),st')
  | Add(Const(n1),Const(n2)) -> (Const(n1+n2),st)
  | Add(Const(n1),e2) -> let (e2',st') = trace1_expr st e2 in (Add(Const(n1),e2'),st')
  | Add(e1,e2) -> let (e1',st') = trace1_expr st e1 in (Add(e1',e2),st')
  | Sub(Const(n1),Const(n2)) -> (Const(n1-n2),st)
  | Sub(Const(n1),e2) -> let (e2',st') = trace1_expr st e2 in (Sub(Const(n1),e2'),st')
  | Sub(e1,e2) -> let (e1',st') = trace1_expr st e1 in (Sub(e1',e2),st')
  | Mul(Const(n1),Const(n2)) -> (Const(n1*n2),st)
  | Mul(Const(n1),e2) -> let (e2',st') = trace1_expr st e2 in (Mul(Const(n1),e2'),st')
  | Mul(e1,e2) -> let (e1',st') = trace1_expr st e1 in (Mul(e1',e2),st')
  | Eq(Const(n1),Const(n2)) -> if n1=n2 then (True,st) else (False,st)
  | Eq(Const(n1),e2) -> let (e2',st') = trace1_expr st e2 in (Eq(Const(n1),e2'),st')
  | Eq(e1,e2) -> let (e1',st') = trace1_expr st e1 in (Eq(e1',e2),st')
  | Leq(Const(n1),Const(n2)) -> if n1<=n2 then (True,st) else (False,st)
  | Leq(Const(n1),e2) -> let (e2',st') = trace1_expr st e2 in (Leq(Const(n1),e2'),st')
  | Leq(e1,e2) -> let (e1',st') = trace1_expr st e1 in (Leq(e1',e2),st')
  | _ -> raise NoRuleApplies
    

(* Function that execute 1 step of the small-step semantic for commands *)
and trace1_cmd = function
  | St _ -> raise NoRuleApplies
  | Cmd(c,st) -> match c with
        Skip -> St st

      | Break -> St (getenv st, getmem st, getloc st, Br)

      (* We can only assign constant values, so if an expression isn't evaluated to a constant, it performs small-steps until it becomes a constant *)
      | Assign(x,Const(n)) -> (match topenv st x with
          IVar l -> St (getenv st, bind (getmem st) l n, getloc st, Continue)
        | _ -> raise (TypeError ("Error on assignment to variable" ^ x)))
      | Assign(x,e) -> let (e',st') = trace1_expr st e in Cmd(Assign(x,e'),st')

      (* We can only assign constant values, so if an expression isn't evaluated to a constant, it performs small-steps until it becomes a constant *)
      (* Also, if the index of the array cell itself isn't evaluated to a constant it performs small-steps until it becomes a constant *)
      | Assign_cell(a, Const(i), Const(n)) -> ( match topenv st a with
          | IArr(l, dim) when i < dim -> St (getenv st, bind (getmem st) (l+i) n, getloc st, Continue)
          | IArr(_, dim) -> raise (OOB("OOB: trying to access array " ^ a ^ " with dim " ^ string_of_int dim ^ " with index " ^ string_of_int i))
          | _ -> raise (TypeError ("Trying to access a cell of a non-array object")))
      | Assign_cell(a, Const(i), e2) -> let (e2', st') = trace1_expr st e2 in Cmd(Assign_cell(a, Const(i), e2'), st')
      | Assign_cell(a, e1 ,e2) -> let (e1', st') = trace1_expr st e1 in Cmd(Assign_cell(a, e1', e2), st')

        (* In case the first command changes the flag of the state to Br, the program need to be shut down, so the function does not evaluate c2*)
      | Seq(c1,c2) -> (match trace1_cmd (Cmd(c1,st)) with
            | St (envl, mem, l, Br)
            | Cmd(_, (envl, mem, l, Br)) -> St (envl, mem, l, Br) 
            | St st1 -> Cmd(c2,st1)
            | Cmd(c1',st1) -> Cmd(Seq(c1',c2),st1))
        
        (* If the expression to check isn't True/False the function keeps performing small-steps until the expression becomes one of such expressions*)
      | If(True,c1,_) -> Cmd(c1,st)
      | If(False,_,c2) -> Cmd(c2,st)
      | If(e,c1,c2) -> let (e',st') = trace1_expr st e in Cmd(If(e',c1,c2),st')

      (* To keep trace of the original command of the repeat, the function returns the step after calling the Repeat_exec. It needs to do effective step, 
         so returning the Repeat_exec without one step of the trace would result in a "duplicate step", since it does not change anything *)
      | Repeat(c) ->  trace1_cmd(Cmd(Repeat_exec(c, c), st))

      (* The first command is the one to store, the second one is the one to execute, if at some point the flag of the state is changed to Br,
         the expected behaviour would be to interrupt the execution of only the repeat construct and not the whole program, so the flag will be chenged to
        Continue without continuing the execution of the source_cmd*)
      | Repeat_exec(source_cmd, c) -> (match trace1_cmd (Cmd(c, st)) with
        | St (envl, mem, l, Br) 
        | Cmd(_, (envl, mem, l, Br)) -> St (envl, mem, l, Continue)
        | St st' -> Cmd(Repeat_exec(source_cmd, source_cmd), st')
        | Cmd(c', st') -> Cmd(Repeat_exec(source_cmd, c'), st')
      )

      (* This represents a block containing declarations and commands, it performes the declarations, keeping track of the chenges to the state by pushing 
         the new environment into the environment list, and it leaves the execution of the commands to the Block *)
      | Decl(dv, c) ->
          let (e', l') = sem_decl_dv (topenv st, getloc st) dv in
          let st' = (e'::(getenv st), getmem st, l', Continue) in
          Cmd(Block(c), st')
      
      (* This represent a block of commands, after the execution of such commands if concluded, this costruct pops the top environment from the list so that
         when the execution returns to the upper block the environment at the top of the list is the one that was being used before the current Block *)
      | Block(c) -> (match trace1_cmd (Cmd(c, st)) with
             Cmd(c', st1) -> Cmd(Block(c'), st1)
            | St st1 -> St(popenv st, getmem st1, getloc st1, Continue)
            )
      
      (* This represents the calling of a procedure previously declarated, the declaration of the parameters will result in a push of a new environment, 
         and the execution of the command block of the procedure will pop this environment *)
      (* In this case the actual parameter that is being passed to the procedure is already evaluated to a constant, which means that is can only be passed by value *)
      | Call_proc(f, Pa(Const(n))) -> (match topenv st f with
          | IProc(pf, c) -> (match pf with
            | Val x ->
                 let l = getloc st in
                 let (e', l') = sem_decl_dv (topenv st, l) (Var_decl(x)) in
                 let mem' = bind (getmem st) l n in 
                 Cmd(Block(c), (e'::getenv st, mem', l', Continue))
                 
            | Ref x -> raise (ConstByRef (x, n)) 
          )
          | _ -> raise (TypeError "Cannot call a non callable object") 
      )
      
      (* In this case, the actual parameter is a ide of some sort *)
      | Call_proc(f, Pa(Var(z))) -> (match topenv st f with
          | IProc(pf, c) -> (match pf with
              
              (* In case the formal parameter is passed by value...*)
            | Val x -> (match topenv st z with
              
                  (* ...and the actual parameter is a variable, the function simply allocates new space for the formal parameter and return Call_proc after evaluating 
                     the atual parameter to a constant*)
                | IVar _ -> 
                    let val_z = apply st z in 
                    Cmd(Call_proc(f, Pa(Const(val_z))), st)
                  
                  (* ... and the actual parameter is an array, the function allocates new space for the function array and copies the values of the actual parameter
                    into the new locations allocated*)
                | IArr (l_start, dim)->
                    let l = getloc st in 
                    let (e', l') = sem_decl_dv (topenv st, l) (Array_decl(x, dim)) in
                    let mem' = copy_array (getmem st) l_start l dim in 
                    Cmd(Block(c), (e'::getenv st, mem', l', Continue))
                
                (* ... and the actual parameter is a procedure, the function raises an exception since we don't admit high order functions *)
                | IProc(_,_)-> raise (TypeError "Cannot pass a function by parameter")
            )
            
            (* In case the formal parameter is passed by reference the function binds the value of the actual parameter in the environment to the formal one
                in a new environment*)
            | Ref x ->
              let lx = topenv st z in 
              let e' = bind (topenv st) x lx in 
              Cmd(Block(c), (e'::getenv st, getmem st, getloc st, Continue))
          )
          | _ -> raise (TypeError "Cannot call a non callable object") 
      )

      (* In this case the actual parameter is the cell of an array *)
      | Call_proc(f, Pa(Array(a, Const(i)))) -> ( match topenv st f with
          | IProc(pf, c) -> (match pf with

              (* If it's passed by value, the function evaluates such value and calls the Call_proc with a new constant as the actual parameter*)
              Val _ -> 
                let val_cell = apply_arr st a i in 
                Cmd(Call_proc(f, Pa(Const(val_cell))), st)
            
                (* If it's passed by reference, the function checks that the ide used to index a cell actually refers to an array in the environment
                   and that it does not go out of bound, if so, it binds the location of the given cell to the formal parameter and pushed the new 
                    environment *)
            | Ref x -> (match topenv st a with
              | IArr(l, d) when i < d-> 
                  let lx = IVar(l+1) in 
                  let e' = bind (topenv st) x lx in
                  Cmd(Block(c), (e'::getenv st, getmem st, getloc st, Continue))
              | _ -> raise (TypeError (a ^ " is not an array, cant use the index operator"))
            )
          )
              
          | _ -> raise (TypeError "Cannot call a non callable object") 
        )
      
      (* This is the case where the actual parameter still needs to be evaluated more in order to call the procedure *)
      | Call_proc(f, Pa(e)) -> 
        let (e', st') = trace1_expr st e in Cmd(Call_proc(f, Pa(e')), st')

(* This function returns a list consisting in all the steps of the trace of a funtion*)
let rec trace_rec (n : int) t =
  if n<=0 then [t]
  else try
      let t' = trace1_cmd t
      in t::(trace_rec (n-1) t')
    with NoRuleApplies -> [t]

(**********************************************************************
 trace : int -> prog -> conf list

 Usage: trace n c performs n steps of the small-step semantics
 **********************************************************************)
let trace n (Prog(dv, dp, c)) =
  let (e,l) = sem_decl_dv (botenv,0) dv in
  let e' = sem_decl_dp e dp in
  trace_rec n (Cmd(c,([e'],botmem,l, Continue)))
