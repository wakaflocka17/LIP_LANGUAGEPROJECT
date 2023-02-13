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
%left SEQP
%nonassoc PROC
(* %nonassoc PROC  dune says its irrelevant*)
%nonassoc ELSE (* REPEAT idem^^^^*)
%left OR
%left AND
%nonassoc NOT
%left EQ LEQ
%left PLUS MINUS
%left MUL

%start <program> prog 

%% (* Grammar *)

prog:
    | decl_var = dv; SEQ; decl_params = dp; SEQ; c = cmd ; EOF { Prog(decl_var, decl_params, c) }
    | decl_var = dv; SEQ; c = cmd ; EOF { Prog(decl_var, Nullproc, c) }
    | c = cmd; EOF { Prog(Nullvar, Nullproc, c) }
;

expr:
    | TRUE { True }
    | FALSE { False }
    | n = CONST { Const(int_of_string n) }
    | NOT; e=expr { Not e }
    | e1=expr; AND; e2=expr { And(e1,e2) }
    | e1=expr; OR; e2=expr { Or(e1,e2) }
    | e1=expr; PLUS; e2=expr { Add(e1,e2) }
    | e1=expr; MINUS; e2=expr { Sub(e1,e2) }
    | e1=expr; MUL; e2=expr { Mul(e1,e2) }
    | e1=expr; EQ; e2=expr { Eq(e1,e2) }
    | e1=expr; LEQ; e2=expr { Leq(e1,e2) }
    | x = IDE { Var(x) }
    | a = IDE; LSQUARE; e = expr; RSQUARE; { Array(a ,e) }
    | LPAREN; e=expr; RPAREN { e }
;

dv:
    | INT; x = IDE; { Var_decl(x) }
    | ARRAY; a = IDE; LSQUARE; dim = CONST; RSQUARE; { Array_decl(a, int_of_string dim)}
    | dv1 = dv; SEQ; dv2 = dv; { Seq_dv(dv1, dv2) }
    | { Nullvar }
;


dp:
    | dp1 = dp; dp2 = dp; { Seq_dp(dp1, dp2) } %prec SEQP
    | PROC; f = IDE; LPAREN; formal_p = pf; RPAREN; LBRACE; c = cmd; RBRACE; { Proc_decl(f, formal_p, c) }
;

pf: 
    | VAL; x = IDE; { Val(x) }
    | REF; x = IDE; { Ref(x) }
;

pa: 
    | e = expr; { Pa(e) }

cmd:
    | SKIP { Skip }
    | BREAK { Break }
    | x = IDE; ASSIGN; e = expr; { Assign(x, e) }
    | a = IDE; LSQUARE; e1 = expr; RSQUARE; ASSIGN; e2 = expr; { Assign_cell(a, e1, e2) } 
    | c1 = cmd; SEQ; c2 = cmd;{ Seq(c1, c2) }
    | REPEAT; c = cmd; FOREVER; { Repeat(c) }
    | IF; e = expr; THEN; c1 = cmd; ELSE; c2 = cmd; { If(e, c1, c2) }
    | LBRACE; d = dv; SEQ; c = cmd; RBRACE; { Decl(d, c) }
    | LBRACE; c = cmd; RBRACE; { Decl(Nullvar, c) }
    | f = IDE; LPAREN; p = pa; RPAREN; { Call_proc(f, p) }
    | LPAREN; c = cmd; RPAREN; {c}
;