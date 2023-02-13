open Ast
open Types
open Main

let string_of_val = function
  n -> string_of_int n


let rec string_of_expr = function
  | True -> "true"
  | False -> "false"
  | Const n -> string_of_int n
  | Not e -> "not" ^ string_of_expr e
  | And(e1,e2) -> string_of_expr e1 ^ " and " ^ string_of_expr e2
  | Or(e1,e2) -> string_of_expr e1 ^ " or " ^ string_of_expr e2
  | Add(e1,e2) -> string_of_expr e1 ^ "+" ^ string_of_expr e2
  | Sub(e1,e2) -> string_of_expr e1 ^ "-" ^ string_of_expr e2
  | Mul(e1,e2) -> string_of_expr e1 ^ "*" ^ string_of_expr e2
  | Eq(e1,e2) -> string_of_expr e1 ^ "=" ^ string_of_expr e2
  | Leq(e1,e2) -> string_of_expr e1 ^ "<=" ^ string_of_expr e2
  | Var(x) -> x
  | Array(a, e) -> a ^ "[" ^ string_of_expr e ^ "]"


let rec string_of_dv = function
  | Var_decl(x) -> "int " ^ x 
  | Array_decl(a, dim) -> "int " ^ a ^ "[" ^ string_of_int dim ^ "]"
  | Seq_dv(dv1, dv2) -> string_of_dv dv1 ^ "; " ^ string_of_dv dv2
  | Nullvar -> ""


let string_of_pf = function
  | Val(x) -> "val " ^ x
  | Ref(x) -> "ref " ^ x

let string_of_pa = function
  | Pa(e) -> string_of_expr e

let rec string_of_cmd = function
  | Skip -> "skip"
  | Break -> "break"
  | Assign(x,e) -> x ^ ":=" ^ string_of_expr e
  | Assign_cell(a, e1, e2) -> a ^ "[" ^ string_of_expr e1 ^ "]:=" ^ string_of_expr e2
  | Seq(c1,c2) -> string_of_cmd c1 ^ "; " ^ string_of_cmd c2
  | Repeat(c) -> "repeat " ^ string_of_cmd c ^ " forever"
  | If(e,c1,c2) -> "if " ^ string_of_expr e ^ " then " ^ string_of_cmd c1 ^ " else " ^ string_of_cmd c2
  | Decl(Nullvar, c) -> "{ " ^ string_of_cmd c ^ "}"
  | Decl(d, c) -> "{ " ^ string_of_dv d ^ "; " ^ string_of_cmd c ^ "}"
  | Call_proc(f, p) -> f ^ "(" ^ string_of_pa p ^ ")"
  | Block(c) -> "{ " ^ string_of_cmd c ^ " }"

let rec string_of_dp = function
  | Nullproc -> ""
  | Proc_decl(f, formal_p, c) -> f ^ "(" ^ string_of_pf formal_p ^ ") {" ^ string_of_cmd c ^ "} "
  | Seq_dp(dp1, dp2) -> string_of_dp dp1 ^ string_of_dp dp2

  let string_of_prog = function
  | Prog(decl_var, Nullproc, c) -> string_of_dv decl_var ^ "; " ^ string_of_cmd c
  | Prog(decl_var, decl_params, c) -> string_of_dv decl_var ^ "; " ^ string_of_dp decl_params ^ "; " ^ string_of_cmd c


let string_of_pf = function
  | Val x -> x
  | Ref x -> x

let string_of_env1 s x = match topenv s x with
  | IVar l -> string_of_int l ^ "/" ^ x
  | IArr (l, dim) -> string_of_int l ^ "[" ^ string_of_int dim ^ "]" ^ x
  | IProc(pf,c) -> "(" ^ string_of_pf pf ^ ", " ^ string_of_cmd c ^ ")" ^ x

    
let string_of_env (s : state) vars =
  let env = topenv s in
  let dom = List.filter (fun x -> try let _ = env x in true with _ -> false) vars in
  let rec helper = function
    [] -> ""
  | [x] -> string_of_env1 s x
  | x::dom' -> string_of_env1 s x ^ "," ^ helper dom'

  in helper dom


let string_of_mem1 (m,l) i =
  assert (i<l);
  string_of_val (m i) ^ "/" ^ string_of_int i

let rec range a b = if b<a then [] else a::(range (a+1) b);;

let string_of_mem (m,l) =
  List.fold_left (fun str i -> str ^ (try string_of_mem1 (m,l) i ^ "," with _ -> "")) "" (range 0 (l - 1))

let string_of_status = function
  | Continue -> "Continue"
  | Br -> "Break"

let rec getArrLocs l dim = match dim with
| 0 -> []
| _ -> l::getArrLocs (l+1) (dim-1)

let rec getlocs e = function
    [] -> []
  | x::dom -> try (match e x with
    | IVar l -> l::(getlocs e dom)
    | IArr(l, dim) -> getArrLocs l dim @ getlocs e dom
    | IProc(_,_) -> [])
    with _ -> getlocs e dom


let string_of_state st dom =
  "[" ^ string_of_env st dom ^ "], " ^
  "[" ^ string_of_mem (getmem st,getloc st) ^ "]" ^ ", " ^
  string_of_int (getloc st) ^ ", " ^ string_of_status (getstatus st)


  let rec union l1 l2 = match l1 with
  [] -> l2
| x::l1' -> (if List.mem x l2 then [] else [x]) @ union l1' l2


let rec vars_of_expr = function
  True
| False
| Const _ -> []
| Array(x, _) -> [x]
| Var x -> [x]
| Not e -> vars_of_expr e
| And(e1,e2) 
| Or(e1,e2) 
| Add(e1,e2)
| Sub(e1,e2)
| Mul(e1,e2)      
| Eq(e1,e2) 
| Leq(e1,e2) -> union (vars_of_expr e1) (vars_of_expr e2)

and vars_of_pa = function 
  | Pa e -> vars_of_expr e

and vars_of_pf = function
  | Val x -> [x]
  | Ref x -> [x]

and vars_of_dv = function
    Nullvar -> []
  | Var_decl(x) -> [x]
  | Array_decl(x, _) -> [x]
  | Seq_dv(d1,d2) -> union (vars_of_dv d1) (vars_of_dv d2)    

and vars_of_cmd = function
    Skip -> []
  | Break -> []
  | Assign(x,e) -> union [x] (vars_of_expr e)
  | Assign_cell(x, e1, e2) -> union [x] (union (vars_of_expr e1) (vars_of_expr e2))
  | Seq(c1,c2) -> union (vars_of_cmd c1) (vars_of_cmd c2)
  | Repeat c -> vars_of_cmd c
  | If(e,c1,c2) -> union (vars_of_expr e) (union (vars_of_cmd c1) (vars_of_cmd c2))                 
  | Decl(dv, c) -> union (vars_of_dv dv) (vars_of_cmd c)
  | Call_proc(f, p) -> union [f] (vars_of_pa p) 
  | Block(c) -> vars_of_cmd c        

and vars_of_dp = function
  | Nullproc -> []
  | Proc_decl(f, pf, c) -> union [f] (union (vars_of_pf pf) (vars_of_cmd c))
  | Seq_dp(dp1, dp2) -> union (vars_of_dp dp1) (vars_of_dp dp2)


let vars_of_prog (Prog(dv, dp, c)) = union (vars_of_dv dv) (union (vars_of_dp dp) (vars_of_cmd c))

let string_of_conf vars = function
  St st -> string_of_state st vars
| Cmd(c,st) -> "<" ^ string_of_cmd c ^ ", " ^ string_of_state st vars ^ ">"


let rec string_of_trace vars = function
  [] -> ""
| [x] -> (string_of_conf vars x)
| x::l -> (string_of_conf vars x) ^ "\n -> " ^ string_of_trace vars l


let rec last = function
  [] -> failwith "last on empty list"
| [x] -> x
| _::l -> last l

let print_trace ps n  =
  let p = parse ps in
  try (
  let t = last (trace n p) in (* actual result *)
  print_string (ps ^ " ->* " ^ string_of_conf (vars_of_prog p) t);
  )
  with
  (* generic error-handling *)
    _ -> print_string("error for this program")
