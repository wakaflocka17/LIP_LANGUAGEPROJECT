
(* The type of tokens. *)

type token = 
  | VAL
  | TRUE
  | THEN
  | SKIP
  | SEQ
  | RSQUARE
  | RPAREN
  | REPEAT
  | REF
  | RBRACE
  | PROC
  | PLUS
  | OR
  | NOT
  | MUL
  | MINUS
  | LSQUARE
  | LPAREN
  | LEQ
  | LBRACE
  | INT
  | IF
  | IDE of (string)
  | FOREVER
  | FALSE
  | EQ
  | EOF
  | ELSE
  | CONST of (string)
  | BREAK
  | ASSIGN
  | ARRAY
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.program)
