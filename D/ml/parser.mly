%{
open Utils;;
%}
%token <string> VAR
%token AND OR NOT
%token LEFT_BR RIGHT_BR
%token IMPLY COMMA EMPTY
%token EOF
%right IMPLY
%left OR
%left AND
%nonassoc NOT
%start main
%type <Utils.expr> main
%%
main:
        exp EOF                 { $1 }
exp:
        VAR                     { Variable ($1) }            
        | LEFT_BR exp RIGHT_BR  { $2 }     
        | NOT exp               { Not ($2) }  
        | exp IMPLY exp         { Call (Imply, $1, $3) }
        | exp AND exp           { Call (And, $1, $3) }
        | exp OR exp            { Call (Or, $1, $3) }
        | EMPTY                 { FalseExpr }
        