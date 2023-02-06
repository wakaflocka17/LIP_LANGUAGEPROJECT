type ide = string (* Ide -> name variable *)

(* Espressioni *)
type expr =
  | True
  | False
  | Const of int     
  | Not of expr
  | And of expr * expr
  | Or of expr * expr
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr
  | Eq of expr * expr
  | Leq of expr * expr
  | Var of ide
  | Array of ide * expr

(* Parametri formali *)
type pf = 
  | Val of ide  (* Parameters passed by value *)
  | Ref of ide  (* Parameters passed by reference *)

(* Parametri attuale *)
type pa = Pa of expr

(* Dichiarazioni Variabili *)
type dv = 
  | Nullvar
  | Seq_dv of dv * dv            (* Multiple declarations *)
  | Var_decl of ide              (* Declaration of a variable *)
  | Array_decl of ide * int      (* Declaration of an array *)

(* Comandi *)
type cmd = 
  | Skip
  | Break
  | Assign of ide * expr                  (* Assigning a expr to a variable *)
  | Assign_cell of ide * expr * expr      (* Assigning a expr to an element of an array*)
  | Seq of cmd * cmd
  | Repeat of cmd
  | If of expr * cmd * cmd
  | Block of dv * cmd                     (* Block containing declarations of variables and cmd*)
  | Call of ide * pa                      (* Calling a procedure *)

(* Dichiarazioni Procedure *)
type dp = 
  | Nullproc                
  | Seq_dp of dp * dp              (* Multiple declarations *)
  | Proc_decl of ide * pf * cmd    (* Declaration of a precedure *)

(* Programma *)
type program = Prog of dv * dp * cmd
