{
module Parser where
import Utils
import Lexer
}

%name         parseProof
%tokentype    { LogicToken }
%error        { logicParseError }

%token
  VAR  { VarTkn $$ }
  "("  { LeftBrTkn }
  ")"  { RightBrTkn }
  "&"  { AndTkn }
  "->" { ImplyTkn }
  "!"  { NotTkn }
  "|"  { OrTkn }
  "|-" { TurnstileTkn }
  ","  { CommaTkn }
%%

ProofString: Context "|-" Expr { ProofLine (Context $1) $3 }

Context: Expr "," Context   { $1 : $3 }
       | Expr               { [$1] }
       | {- none -}         { [] }

Expr: Disjunction           { $1 } 
    | Disjunction "->" Expr { Call Imply $1 $3 }

Disjunction: Conjunction                  { $1 } 
           | Disjunction "|" Conjunction  { Call Or $1 $3 }

Conjunction: Negation                 { $1 }
           | Conjunction "&" Negation { Call And $1 $3 }

Negation: "!" Negation { Not $2 } 
        | VAR          { Variable $1 } 
        | "(" Expr ")" { $2 }
