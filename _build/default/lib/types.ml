open Ast
    
type loc = int
type status = Continue | Br

type envval = IVar of loc | IArr of loc * int | IProc of pf * cmd
type memval = int

type env = ide -> envval
type mem = loc -> memval

(* The third component of the state is the first free location.
   We assume that the store is unbounded *)
type state = env list * mem * loc * status

let topenv (el,_,_,_) = match el with
    [] -> failwith "empty environment stack"
  | e::_ -> e

let popenv (el,_,_,_) = match el with
    [] -> failwith "empty environment stack"
  | _::el' -> el'

let getenv (el,_,_, _) = el
let getmem (_,m,_, _) = m
let getloc (_,_,l, _) = l

let getstatus (_,_,_,stat) = stat
  
type conf = St of state | Cmd of cmd * state

exception TypeError of string
exception UnboundVar of ide
exception UnboundLoc of int
exception NoRuleApplies
exception ConstByRef of ide * int
exception OOB of string