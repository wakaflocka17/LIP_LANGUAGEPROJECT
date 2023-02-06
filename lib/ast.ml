type ide = string (* Ide -> name variable *)

(* Dichiarazioni Variabili *)
type dv = 
  | nullvar
  | seq_dv of dv * dv       (* Multiple declarations *)
  | var of ide              (* Declaration of a variable *)
  | array of ide * int      (* Declaration of an array *)

(* Dichiarazioni Procedure *)

(* Espressioni *)

(* Comandi *)

(* Parametri formali *)

(* Parametri attuale *)

(* Programma *)