{
module Lexer where
-- import Data.Char
}

%wrapper "basic"

tokens :-
  $white+    ;
  ([0-9]+)   {NumberTkn . read}
  \w         {const OmegaTkn}
  \(         {const LeftBrTkn}
  \)         {const RightBrTkn}
  \+         {const AddTkn}
  \*         {const MulTkn}
  \^         {const PowTkn}
  \=         {const EquTkn}

{ 
data OrdinalToken = NumberTkn Int | OmegaTkn | LeftBrTkn | RightBrTkn | AddTkn | MulTkn | PowTkn | EquTkn deriving (Eq, Show) 

{-
tokenize :: [Char] -> [Token]
tokenize [] = []
tokenize ('=':t) = EquTkn : tokenize t
tokenize ('+':t) = AddTkn : tokenize t
tokenize ('*':t) = MulTkn : tokenize t
tokenize ('^':t) = PowTkn : tokenize t
tokenize ('(':t) = LeftBrTkn  : tokenize t
tokenize (')':t) = RightBrTkn : tokenize t
tokenize ('w':t) = OmegaTkn : tokenize t
tokenize (h:t)
  | isSpace h = tokenize t
  | isDigit h = NumberTkn (read $ h : digs) : tokenize rest
    where
      (digs, rest) = span isDigit t
-}

}

