%{
open Ast
%}

%token TRUE
%token FALSE
%token NOT
%token AND
%token OR
%token PLUS
%token MINUS
%token MUL
%token EQ
%token LEQ
%token <string> IDE
%token <string> CONST

%token SKIP
%token TAKES
%token SEQ
%token IF
%token THEN
%token ELSE
%token WHILE
%token DO

%token LPAREN
%token RPAREN
%token LBRACE
%token RBRACE
%token EOF