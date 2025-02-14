{
module Parser where
import Utils
import Lexer
}

%name         parseProof
%tokentype    { LogicToken }
%error        { logicParseError }

%token
  VAR   { VarTkn $$ }
  "("   { LeftBrTkn }
  ")"   { RightBrTkn }
  "&"   { AndTkn }
  "->"  { ImplyTkn }
  "!"   { NotTkn }
  "|"   { OrTkn }
  "|-"  { TurnstileTkn }
  ","   { CommaTkn }
  "_|_" { EmptyTkn }
%%


Expr: Disjunction           { $1 } 
    | Disjunction "->" Expr { Call Imply $1 $3 }

Disjunction: Conjunction                  { $1 } 
           | Disjunction "|" Conjunction  { Call Or $1 $3 }

Conjunction: Negation                 { $1 }
           | Conjunction "&" Negation { Call And $1 $3 }

Negation: "!" Negation { Not $2 } 
        | VAR          { Variable $1 } 
        | "_|_"        { FalseExpr }
        | "(" Expr ")" { $2 }
