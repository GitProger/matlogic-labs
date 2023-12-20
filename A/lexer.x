{ module Lexer where }

%wrapper "basic"

tokens :-
  $white+ ;
  [A-Z][A-Z 0-9\'’]* {\n -> Var n}
  \(   {const LeftBr}
  \)   {const RightBr}
  \&   {const And}
  "->" {const Imply}
  \!   {const Not}
  \|   {const Or}

{

data LogicToken = Var String | LeftBr | RightBr | And | Imply | Not | Or deriving (Eq)
instance Show LogicToken where
  show (Var nm) = nm
  show x = case x of
             LeftBr -> "("
             RightBr -> ")"
             And -> "&"
             Imply -> "->"
             Not -> "!"
             Or -> "|"
}


