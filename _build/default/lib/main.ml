open Ast
open Types

let apply st x = match topenv st x with
    IVar l -> getmem st l
  | _ -> raise (TypeError "apply error")

let apply_arr st a i = match topenv st a with
  | IArr(l, dim) when i < dim -> getmem st (l+i)
  | IArr(_, dim) -> raise (OOB("OOB: trying to access array " ^ a ^ " with dim " ^ string_of_int dim ^ " with index " ^ string_of_int i))
  | _ -> raise (TypeError "apply_arr error")

let parse (s : string) : program =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog Lexer.read lexbuf in
  ast
;;

(******************************************************************************)
(*                      Small-step semantics of commands                      *)
(******************************************************************************)

exception NoRulesApplies

let botenv = fun x -> raise (UnboundVar x)
let botmem = fun l -> raise (UnboundLoc l)
let bind f x v = fun x' -> if x'=x then v else f x'

let rec sem_decl_dv (e,l) = function
    Nullvar -> (e,l)
  | Var_decl(x) ->  let e' = bind e x (IVar l) in (e',l+1)
  | Array_decl(a, dim) -> let e' = bind e a (IArr (l, dim)) in (e', l+dim)
  | Seq_dv(dv1, dv2) -> 
      let (e', l') = sem_decl_dv (e, l) dv1 in sem_decl_dv (e', l') dv2


let rec sem_decl_dp e = function
    | Nullproc -> e
    | Proc_decl(f, pf, c) -> let e' = bind e f (IProc(pf, c)) in e'
    | Seq_dp(dp1, dp2) -> 
      let e' = sem_decl_dp e dp1 in sem_decl_dp e' dp2

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

and trace1_cmd = function
  | St _ -> raise NoRuleApplies
  | Cmd(c,st) -> match c with
        Skip -> St st

      | Break -> St (getenv st, getmem st, getloc st, Br)

      | Assign(x,Const(n)) -> (match topenv st x with
          IVar l -> St (getenv st, bind (getmem st) l n, getloc st, Continue)
        | _ -> raise (TypeError ("Error on assignment to variable" ^ x)))
      | Assign(x,e) -> let (e',st') = trace1_expr st e in Cmd(Assign(x,e'),st')


      | Assign_cell(a, Const(i), Const(n)) -> ( match topenv st a with
          | IArr(l, dim) when i < dim -> St (getenv st, bind (getmem st) (l+i) n, getloc st, Continue)
          | _ -> raise (TypeError ("Error on assignment to array " ^ a ^ " on location " ^ string_of_int i ^ " out of bound"))
      )
      | Assign_cell(a, Const(i), e2) -> let (e2', st') = trace1_expr st e2 in Cmd(Assign_cell(a, Const(i), e2'), st')
      | Assign_cell(a, e1 ,e2) -> let (e1', st') = trace1_expr st e1 in Cmd(Assign_cell(a, e1', e2), st')


      | Seq(c1,c2) -> (match trace1_cmd (Cmd(c1,st)) with
            | St (envl, mem, l, Br)
            | Cmd(_, (envl, mem, l, Br)) -> St (envl, mem, l, Br) 
            | St st1 -> Cmd(c2,st1)
            | Cmd(c1',st1) -> Cmd(Seq(c1',c2),st1))
        
      | If(True,c1,_) -> Cmd(c1,st)
      | If(False,_,c2) -> Cmd(c2,st)
      | If(e,c1,c2) -> let (e',st') = trace1_expr st e in Cmd(If(e',c1,c2),st')

      | Repeat(c) ->  trace1_cmd(Cmd(Repeat_exec(c, c), st))

      | Repeat_exec(source_cmd, c) -> (match trace1_cmd (Cmd(c, st)) with
        | St (envl, mem, l, Br) 
        | Cmd(_, (envl, mem, l, Br)) -> St (envl, mem, l, Continue)
        | St st' -> Cmd(Repeat_exec(source_cmd, source_cmd), st')
        | Cmd(c', st') -> Cmd(Repeat_exec(source_cmd, c'), st')
      )

      | Decl(dv, c) ->
          let (e', l') = sem_decl_dv (topenv st, getloc st) dv in
          let st' = (e'::(getenv st), getmem st, l', Continue) in
          Cmd(Block(c), st')

      | Block(c) -> (match trace1_cmd (Cmd(c, st)) with
             Cmd(c', st1) -> Cmd(Block(c'), st1)
            | St st1 -> St(popenv st, getmem st1, getloc st1, Continue)
            )
      
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

      | Call_proc(f, Pa(Var(z))) -> (match topenv st f with
          | IProc(pf, c) -> (match pf with
            | Val _ ->
                 let val_z = apply st z in 
                 Cmd(Call_proc(f, Pa(Const(val_z))), st)
                 
            | Ref x ->
              let lx = topenv st z in 
              let e' = bind (topenv st) x lx in 
              Cmd(Block(c), (e'::getenv st, getmem st, getloc st, Continue))
          )
          | _ -> raise (TypeError "Cannot call a non callable object") 
      )
      | Call_proc(f, Pa(e)) -> 
        let (e', st') = trace1_expr st e in Cmd(Call_proc(f, Pa(e')), st')
      
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
