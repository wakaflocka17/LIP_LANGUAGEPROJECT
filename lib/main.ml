open Ast
open Types

let apply st x = match topenv st x with
    IVar l -> getmem st l
  | _ -> failwith "apply error"

let apply_arr st a i = match topenv st a with
  | IArr(l, dim) when i < dim -> getmem st (l+i)
  | IArr(_, dim) -> failwith ("OOB: trying to access array " ^ a ^ " with dim " ^ string_of_int dim ^ " with index " ^ string_of_int i)
  | _ -> failwith "error with apply_arr"

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

let rec sem_decl_dv (e,l) = function
    Nullvar -> (e,l)
  | Var_decl(x) ->  let e' = bind e x (IVar l) in (e',l+1)
  | Array_decl(a, dim) -> let e' = bind e a (IArr (l, dim)) in (e', l+dim)
  | Seq_dv(dv1, dv2) -> 
      let (e', l') = sem_decl_dv (e, l) dv1 in sem_decl_dv (e', l') dv2

let rec sem_decl_dv_spec (e, l) lmem d = 
  if l = lmem then sem_decl_dv (e, l) d
  else match d with
  Nullvar -> (e,l)
  | Var_decl(x) ->  let e' = bind e x (IVar lmem) in (e',l)
  | Array_decl(a, dim) -> let e' = bind e a (IArr (lmem, dim)) in (e', l)
  | Seq_dv(dv1, dv2) -> 
      let (e', l') = sem_decl_dv_spec (e, l) lmem dv1 in sem_decl_dv_spec (e', l') lmem dv2


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

  
(*Utils functions, might not need them
and trace_rec_expr st e = try
  let (e', st') = trace1_expr st e
  in e::(trace_rec_expr st' e')
with NoRuleApplies -> [e]

and get_last_trace t = match t with
  | [] -> failwith "No trace avaiable"
  | t'::[] -> t'
  | t'::l -> get_last_trace l

and get_expr_val st e =
  let t = trace_rec_expr st e in  
  let value = get_last_trace t in 
  match value with
    | Const(n) -> n
    | _ -> failwith "The expression does not evaluate correctly"
*)

and trace1_cmd = function
  | St _
  | Br _ -> raise NoRuleApplies
  | Cmd(c,st) -> match c with
        Skip -> St st

      | Break -> Br st

      | Assign(x,Const(n)) -> (match topenv st x with
          IVar l -> St (getenv st, bind (getmem st) l n, getloc st)
        | _ -> failwith ("Error on assignment to variable" ^ x))
      | Assign(x,e) -> let (e',st') = trace1_expr st e in Cmd(Assign(x,e'),st')


      | Assign_cell(a, Const(i), Const(n)) -> ( match topenv st a with
          | IArr(l, dim) when i < dim -> St (getenv st, bind (getmem st) (l+i) n, getloc st)
          | _ -> failwith ("Error on assignment to array " ^ a ^ " on location " ^ string_of_int i ^ " out of bound")
      )
      | Assign_cell(a, Const(i), e2) -> let (e2', st') = trace1_expr st e2 in Cmd(Assign_cell(a, Const(i), e2'), st')
      | Assign_cell(a, e1 ,e2) -> let (e1', st') = trace1_expr st e1 in Cmd(Assign_cell(a, e1', e2), st')


      | Seq(c1,c2) -> (match trace1_cmd (Cmd(c1,st)) with
              St st1 -> Cmd(c2,st1)
            | Br st1 -> St st1
            | Cmd(c1',st1) -> Cmd(Seq(c1',c2),st1))
        
      | If(True,c1,_) -> Cmd(c1,st)
      | If(False,_,c2) -> Cmd(c2,st)
      | If(e,c1,c2) -> let (e',st') = trace1_expr st e in Cmd(If(e',c1,c2),st')

      |Repeat(c) -> (match trace1_cmd (Cmd(c, st)) with
          Br st1 -> Cmd(Skip, st1)
        | St st1 -> Cmd(Repeat(c), st1)
        | Cmd(c', st1) -> Cmd(Seq(c', Repeat(c)), st1)
      )
      | Block(dv, c) ->
          let (e', l') = sem_decl_dv (topenv st, getloc st) dv in
          let st' = (e'::(getenv st), getmem st, l') in
          (match trace1_cmd (Cmd(c, st')) with
             Cmd(c', st1) -> Cmd(Block(Nullvar, c'), st1)
            | St st1
            | Br st1 -> St(popenv st', getmem st1, getloc st1)
          )
      | Call_proc(f, Pa(e)) ->
      


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
