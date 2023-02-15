open Ast
    
type loc = int

type status = Continue | Br (* Represents the status of the execution, if this flag is set to Br the execution need to be terminated *)

type envval = IVar of loc | IArr of loc * int | IProc of pf * cmd     (* Type of values that can occur in the environment *)
type memval = int                                                     (* Type of values that can occur in the memory *)

(* Definition of enviroment and memory *)
type env = ide -> envval
type mem = loc -> memval

(* The third component of the state is the first free location.
   We assume that the store is unbounded *)
type state = env list * mem * loc * status

(* Function that returns the last environment push into the stack*)
let topenv (el,_,_,_) = match el with
    [] -> failwith "empty environment stack"
  | e::_ -> e

(* Function that pops the last environment pushed into the stack *)
let popenv (el,_,_,_) = match el with
    [] -> failwith "empty environment stack"
  | _::el' -> el'

(* Functions to get the environment, memory, next free location  and status of a state *)
let getenv (el,_,_, _) = el
let getmem (_,m,_, _) = m
let getloc (_,_,l, _) = l
let getstatus (_,_,_,stat) = stat

(* Possible configurations of the execution: 
   If set to St it means that there are no more commands to execute
   If set to Cmd it means that there are more commands to execute *)
type conf = St of state | Cmd of cmd * state

(* Type of exception used *)
exception TypeError of string
exception UnboundVar of ide
exception UnboundLoc of int
exception NoRuleApplies
exception ConstByRef of ide * int
exception OOB of string