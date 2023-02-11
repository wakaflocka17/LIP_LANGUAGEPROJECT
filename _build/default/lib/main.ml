open Ast
open Types

let apply st x = match topenv st x with
IVar l -> getmem st l
| _ -> failwith "apply error"

let parse (s : string) : program =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog Lexer.read lexbuf in
  ast
;;

(*
(******************************************************************************)
(*                       Big-step semantics of expressions                    *)
(******************************************************************************)

let rec eval_expr st = function
|  True -> Bool true
|  False -> Bool false
|  Const n -> Int n
|  Var x -> apply st x
| Not(e) -> 
  let v = eval_expr st e in
  (match v with
  | Bool b -> Bool (not b)
  | _ -> raise (TypeError "Not"))
|  And(e1, e2) -> 
  let v1 = eval_expr st e1 in
  let v2 = eval_expr st e2 in
  (match v1, v2 with
  | Bool b1, Bool b2 -> Bool (b1 && b2)
  | _ -> raise (TypeError "And"))
|  Or(e1, e2) ->
  let v1 = eval_expr st e1 in
  let v2 = eval_expr st e2 in
  (match v1, v2 with
  | Bool b1, Bool b2 -> Bool (b1 || b2)
  | _ -> raise (TypeError "Or"))
|  Add(e1, e2) ->
  let v1 = eval_expr st e1 in
  let v2 = eval_expr st e2 in
  (match v1, v2 with
  | Int n1, Int n2 -> Int (n1 + n2)
  | _ -> raise (TypeError "Add"))
|  Sub(e1, e2) ->
  let v1 = eval_expr st e1 in
  let v2 = eval_expr st e2 in
  (match v1, v2 with
  | Int n1, Int n2 -> Int (n1 - n2)
  | _ -> raise (TypeError "Sub"))
|  Mul(e1, e2) ->
  let v1 = eval_expr st e1 in
  let v2 = eval_expr st e2 in
  (match v1, v2 with
  | Int n1, Int n2 -> Int (n1 * n2)
  | _ -> raise (TypeError "Mul"))
|  Eq(e1, e2) ->
  let v1 = eval_expr st e1 in
  let v2 = eval_expr st e2 in
  (match v1, v2 with
  | Int n1, Int n2 -> Bool (n1 = n2)
  | Bool b1, Bool b2 -> Bool (b1 = b2)
  | _ -> raise (TypeError "Eq"))
| Leq(e1, e2) ->
  let v1 = eval_expr st e1 in
  let v2 = eval_expr st e2 in
  (match v1, v2 with
  | Int n1, Int n2 -> Bool (n1 <= n2)
  | _ -> raise (TypeError "Leq"))
| Array(e1, e2) ->
  let v1 = eval_expr st e1 in
  let v2 = eval_expr st e2 in
  (match v1, v2 with
  | Int n1, Int n2 -> Array (n1, n2)
  | _ -> raise (TypeError "Array"))
;;
*)

(******************************************************************************)
(*                      Small-step semantics of commands                      *)
(******************************************************************************)

exception NoRulesApplies

let botenv = fun x -> failwith ("variable " ^ x ^ " unbound")
let botmem = fun l -> failwith ("location " ^ string_of_int l ^ " undefined")
    
let bind f x v = fun x' -> if x'=x then v else f x'

let rec trace1_expr st = function
  | Var x -> (Const(apply st x), st)
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
  | Call(f,Const(n)) -> (match (topenv st) f with
        IFun(x,c,er) ->
        let l = getloc st in
        let env' = bind (topenv st) x (IVar l) in
        let mem' = bind (getmem st) l n in
        let st' = (env'::(getenv st), mem', l+1) in
        (CallExec(c,er),st')
      | _ -> raise (TypeError "Call of a non-function"))
  | Call(f,e) -> let (e',st') = trace1_expr st e in (Call(f,e'),st')
  | CallExec(c,e) -> (match trace1_cmd (Cmd(c,st)) with
      St st' -> (CallRet(e),st')
    | Cmd(c',st') -> (CallExec(c',e),st'))
  | CallRet(Const(n)) -> let st' = (popenv st, getmem st, getloc st) in (Const(n),st')
  | CallRet(e) -> let (e',st') = trace1_expr st e in (CallRet(e'),st')
  | _ -> raise NoRuleApplies

and trace1_cmd = function
    St _ -> raise NoRuleApplies
  | Cmd(c,st) -> match c with
      Skip -> St st
      | Break -> Br st
      | Assign(x,Const(n)) -> (match topenv st x with
          IVar l -> St (getenv st, bind (getmem st) l n, getloc st)
        | _ -> failwith ("Error on assignment to variable" ^ x))
      | Assign(x,e) -> let (e',st') = trace1_expr st e in Cmd(Assign(x,e'),st')
      | Assign_cell(a, Const(i), Const(n)) -> ( match topenv st a with
          | IArr(l, dim) when i < dim -> St (getenv, bind (getmem st) (l+i) n, )
      )
      | Seq(c1,c2) -> (match trace1_cmd (Cmd(c1,st)) with
            St st1 -> Cmd(c2,st1)
            | Br st -> St st
            | Cmd(c1',st1) -> Cmd(Seq(c1',c2),st1))
      | If(True,c1,_) -> Cmd(c1,st)
      | If(False,_,c2) -> Cmd(c2,st)
      | If(e,c1,c2) -> let (e',st') = trace1_expr st e in Cmd(If(e',c1,c2),st')
      | While(e,c) -> Cmd(If(e,Seq(c,While(e,c)),Skip),st)
  

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
  trace_rec n (Cmd(c,([e'],botmem,l)))
