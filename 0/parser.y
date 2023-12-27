{
module Parser where
import Lexer -- https://github.com/ghulette/happy-example/blob/master/Grammar.y
}

%name         parseOrdinals
%tokentype    { OrdinalToken }
%error        { (\toks -> error $ "Parse error in " ++ (show toks)) }

%token
  "("  { LeftBrTkn }
  ")"  { RightBrTkn }
  "+"  { AddTkn }
  "*"  { MulTkn }
  "^"  { PowTkn }
  "="  { EquTkn }
  "w"  { OmegaTkn }
  NAT  { NumberTkn $$ }

%nonassoc   "="
%left       "+"
%left       "*"
%right      "^"

%%

Equation:   Expression "=" Expression { Equation $1 $3 }  -- { Call EquOper $1 $3 }

Expression: Adding                    { $1 } 
            | Expression "+" Adding   { Call Add $1 $3 }

Adding:     Muling                    { $1 }
            | Adding "*" Muling       { Call Mul $1 $3 }

Muling:     Term                      { $1 }
            | Term "^" Muling         { Call Pow $1 $3 }

Term:       "w"                       { Omega }
            | NAT                     { Number $1 }
            | "(" Expression ")"      { $2 }

{

data BiOper = Add | Mul | Pow | Equ deriving Eq
instance Show BiOper where
  show x = case x of
    Add -> "+"
    Mul -> "*"
    Pow -> "^"
    Equ -> "="

data Expression = Number Int | Omega | Call BiOper Expression Expression deriving Eq
instance Show Expression where
  show (Number v) = show v
  show Omega = "w"
  show (Call op a b) = "(" ++ show op ++ "," ++ show a ++ "," ++ show b ++ ")"

data Equation = Equation Expression Expression deriving (Eq, Show)

}

