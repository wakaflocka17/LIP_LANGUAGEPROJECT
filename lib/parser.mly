%{
open Ast
%}

%token <string> CONST
%token PLUS
%token MINUS
%token MUL
%token TRUE
%token FALSE
%token AND
%token OR
%token NOT
%token EQ
%token LEQ
%token <string> IDE
%token ARRAY 
%token INT

%token SKIP
%token BREAK
%token ASSIGN
%token SEQ
%token REPEAT
%token FOREVER
%token IF
%token THEN
%token ELSE
%token PROC

%token VAL
%token REF

%token LPAREN
%token RPAREN
%token LSQUARE
%token RSQUARE
%token LBRACE
%token RBRACE
%token EOF

(* Associativity and precedence *)
%left SEQ
%nonassoc ELSE REPEAT
%left OR
%left AND
%nonassoc NOT
%left EQ LEQ
%left PLUS MINUS
%left MUL

%start <program> prog 

%% (* Grammar *)

prog:
    | dv = decl_v ; dp = decl_p ; c = cmd ; EOF { Prog(dv, dp, c) }
;



