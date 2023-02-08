{
open Parser
}

let white = [' ' '\n' '\t']+                (* Regex for blank spaces *)
let letter = ['a'-'z' 'A'-'Z']              (* Regex for all letters *)
let chr = ['a'-'z' 'A'-'Z' '0'-'9']         (* Regex for letters and digits *)
let ide = letter chr*                        (* Regex for ide *)
let num = ['0'-'9']|['1'-'9']['0'-'9']*     (* Regex for constants *)

rule read =
  parse
  | white { read lexbuf }

  (* Lexing expr *) 
  | "true" { TRUE }
  | "false" { FALSE }
  | "not" { NOT }
  | "and" { AND }
  | "or" { OR }
  | "+" { PLUS }
  | "-" { MINUS }
  | "*" { MUL }  
  | "=" { EQ }
  | "<=" { LEQ }
  | "int" { INT }
  | "array" { ARRAY }

  (* Lexing cmd *)
  | "skip" { SKIP }
  | "break" { BREAK }
  | ":="  { ASSIGN }
  | ";"  { SEQ }
  | "repeat" { REPEAT }
  | "forever" { FOREVER }
  | "if" { IF }
  | "then" { THEN }
  | "else" { ELSE }
  | "proc" { PROC }

  (* Lexing formal parameters *)
  | "val" { VAL }
  | "ref" { REF }

  (* Lexing parenthesis *)
  | "[" { LSQUARE }
  | "]" { RSQUARE }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "{" { LBRACE }
  | "}" { RBRACE }

  (* Lexing variables and constants *)
  | ide { IDE (Lexing.lexeme lexbuf) }
  | num { CONST (Lexing.lexeme lexbuf) }  
  | eof { EOF }