module Utils where
{-# LANGUAGE Strict #-}

import           Data.List (sort, find, intercalate, elem)
import qualified Data.Set as S

------------
-- common --
(~>) = flip (.)

join :: Show a => String -> [a] -> String
join sep a = intercalate sep $ map show a

embrace :: String -> String
embrace s = "[" ++ s ++ "]"

numbered :: Int -> String -> String
numbered n = ((embrace (show n) ++ " ") ++)

takeLastRet :: (a -> Maybe b) -> [a] -> Maybe b
takeLastRet _ [] = Nothing
takeLastRet f (h:t) = case f h of 
  Just r  -> Just r
  Nothing -> takeLastRet f t


double :: (a -> a) -> ((a, a) -> (a, a))
double f = \(a, b) -> (f a, f b)

double2 :: (a -> a -> a) -> ((a, a) -> (a, a) -> (a, a))
double2 f = \(a1, b1) (a2, b2) -> (f a1 a2, f b1 b2)

-------------------
-- lexer helper: --
data LogicToken = VarTkn String 
                | LeftBrTkn | RightBrTkn 
                | AndTkn | ImplyTkn | NotTkn | OrTkn
                | CommaTkn | TurnstileTkn | EmptyTkn deriving (Eq, Ord)
instance Show LogicToken where
  show (VarTkn nm) = nm
  show x = case x of
             LeftBrTkn    -> "("
             RightBrTkn   -> ")"
             AndTkn       -> "&"
             ImplyTkn     -> "->"
             NotTkn       -> "!"
             OrTkn        -> "|"
             TurnstileTkn -> "|-"
             EmptyTkn     -> "_|_"

--------------------
-- parser helper: --
logicParseError :: [LogicToken] -> a
logicParseError _ = error "Parse error"

data BiOper = And | Imply | Or | Dash deriving (Eq, Ord)
instance Show BiOper where
  show x = case x of
             Or -> "|"
             And -> "&"
             Imply -> "->"
             Dash -> "|-"

data Expr = Variable String | Not Expr | Call BiOper Expr Expr | FalseExpr deriving (Eq, Ord)
instance Show Expr where
  show (Variable v)  = v
  show (Not e)       = "(!" ++ (show e) ++ ")"
  show (Call op a b) = "(" ++ show a ++ show op ++ show b ++ ")"
  show FalseExpr     = "_|_"

_I_ = FalseExpr

infixl 7 .&
infixl 6 .|
infixr 5 .->
infixr 4 .|-
        
(.&) :: Expr -> Expr -> Expr
a .& b = (Call And a b)
(.|) :: Expr -> Expr -> Expr
a .| b = (Call Or a b)
(.->) :: Expr -> Expr -> Expr
a .-> b = (Call Imply a b)
(.|-) :: Expr -> Expr -> Expr
a .|- b = (Call Dash a b)
