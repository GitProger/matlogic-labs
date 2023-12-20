{
module Parser where
import Lexer -- https://github.com/ghulette/happy-example/blob/master/Grammar.y

}

%name         parseProof
%tokentype    { LogicToken }
%error        { logicParseError }

%token
  "("  { LeftBr }
  ")"  { RightBr }
  "&"  { And }
  "->" { Imply }
  "!"  { Not }
  "|"  { Or }
  VAR  { Var $$ }
%%

Expr: Disjunction           { $1 } 
    | Disjunction "->" Expr { Call ImplyOper $1 $3 }

Disjunction: Conjunction                  { $1 } 
           | Disjunction "|" Conjunction  { Call OrOper $1 $3 }

Conjunction: Negation                 { $1 }
           | Conjunction "&" Negation { Call AndOper $1 $3 }

Negation: "!" Negation { NotOper $2 } 
        | VAR          { Variable $1 } 
        | "(" Expr ")" { $2 }

{
logicParseError :: [LogicToken] -> a
logicParseError _ = error "Parse error"


data BiOper = AndOper | ImplyOper | OrOper deriving (Eq)
instance Show BiOper where
  show x = case x of
             OrOper -> "|"
             AndOper -> "&"
             ImplyOper -> "->"

data Expr = Variable String | NotOper Expr | Call BiOper Expr Expr
instance Show Expr where
  show (Variable v) = v
  show (NotOper e) = "(!" ++ (show e) ++ ")"
  show (Call op a b) = "(" ++ show op ++ "," ++ show a ++ "," ++ show b ++ ")"


}

