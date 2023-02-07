%{
open Ast
%}

(* Token for expr *)
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

(* Token for cmd *)
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

(* Token for formal parameters *)
%token VAL
%token REF

(* Token for parenthesis *)
%token LPAREN
%token RPAREN
%token LSQUARE
%token RSQUARE
%token LBRACE
%token RBRACE
%token EOF

(* Associativity and precedence *)
%left SEQ
%nonassoc PROC  (* DISCLAIMER MIGHT BE WRONG !!!!!!!!!!!!!!!!!!!!!*)
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
    | decl_var = dv ; decl_params = dp ; c = cmd ; EOF { Prog(decl_var, decl_params, c) }
;

expr: 
    ...
;

dv:
    | INT; x = IDE; { Var_decl(x) }
    | ARRAY; a = IDE; LSQUARE; dim = CONST; RSQUARE; { Array_decl(a, int_of_string dim)}
    | dv1 = dv; SEQ; dv2 = dv; { Seq_dv(dv1, dv2) }
    | { Nullvar }
;

dp:
    | PROC; f = IDE; LPAREN; formal_p = pf; RPAREN; LBRACE; c = cmd; RBRACE; { Proc_decl(f, formal_p, c) }
    | dp1 = dp; dp2 = dp; { Seq_dp(dp1, dp2) } (* might have to add %prec PROC *)
    | { Nullproc }
;

pf: 
    | VAL; x = IDE; { Val(x) }
    | REF; x = IDE; { Ref(x) }
;

pa: 
    | e = expr; { Pa(e) }

cmd:
    ...
;



