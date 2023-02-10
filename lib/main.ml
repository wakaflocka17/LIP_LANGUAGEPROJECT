open Ast
open Types

let apply st x = 
  try List.assoc x st
  with Not_found -> raise (TypeError "Variable not found")
;;

let parse (s : string) : program =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog Lexer.read lexbuf in
  ast
;;


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
  

(******************************************************************************)
(*                      Small-step semantics of commands                      *)
(******************************************************************************)

exception NoRulesApplies

let botenv = fun x -> failwith ("variable " ^ x ^ " unbound")
let botmem = fun l -> failwith ("location " ^ string_of_int l ^ " undefined")
    
let bind f x v = fun y -> if y=x then v else f y