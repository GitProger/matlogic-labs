module Utils where
{-# LANGUAGE Strict #-}

import           Data.List (intercalate, sort)
import qualified Data.Set as S
import qualified Data.Vector as V

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
                | CommaTkn | TurnstileTkn deriving (Eq, Ord)
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

data Expr = Variable String | Not Expr | Call BiOper Expr Expr deriving (Eq, Ord)
instance Show Expr where
  show (Variable v)  = v
  show (Not e)       = "(!" ++ (show e) ++ ")"
  show (Call op a b) = "(" ++ show a ++ show op ++ show b ++ ")"

-------------------------------------------------------------------------------

data Context = Context [Expr] deriving (Eq, Ord)
instance Show Context where
  show (Context e) = join "," e

-- cmpUnord (Context a) (Context b) = sort a == sort b


data ProofLine = ProofLine Context Expr deriving (Eq, Ord)
instance Show ProofLine where
  show (ProofLine ctx e) = show ctx ++ show Dash ++ show e


withCtx ctx (ProofLine _ e) = ProofLine ctx e
withCtxFrom (ProofLine c _) (ProofLine _ e) = ProofLine c e

withSortedCtx (ProofLine (Context c) e) = ProofLine (Context $ sort c) e


getContext (ProofLine c _) = c
getExpr    (ProofLine _ e) = e

expandCtx (ProofLine (Context ctx) (Call Imply a b)) = 
  expandCtx $ ProofLine (Context $ ctx ++ [a]) b  -- a:ctx, because used only sorted 'withSortedCtx' -- ctx ++ [a]
expandCtx p = p


-- better: MarkedExpr ProofLine (MP Int Int)
--                        Res   A   B          Expr,     schema num               from
data MarkedExpr = MP ProofLine Int Int | Axiom ProofLine Int | Deducted ProofLine Int 
                                                             | Hypothesis ProofLine Int 
                                                             | Incorrect ProofLine 
                                                             | MPInc ProofLine Int Int   --
                                                             | DeductedInc ProofLine Int --
instance Show MarkedExpr where
  show (MP e i j)       = show e ++ " " ++ (embrace $ "M.P. " ++ show i ++ ", " ++ show j)
  show (Axiom e n)      = show e ++ " " ++ (embrace $ "Ax. sch. " ++ show n)
  show (Deducted e n)   = show e ++ " " ++ (embrace $ "Ded. " ++ show n)
  show (Hypothesis e n) = show e ++ " " ++ (embrace $ "Hyp. " ++ show n)
  show (Incorrect e)    = show e ++ " " ++ (embrace "Incorrect")
  show (MPInc e i j)     = show e ++ " " ++ (embrace $ "M.P. " ++ show i ++ ", " ++ show j ++ "; from Incorrect")
  show (DeductedInc e n) = show e ++ " " ++ (embrace $ "Ded. " ++ show n ++ "; from Incorrect")

getProofLine :: MarkedExpr -> ProofLine
getProofLine me = case me of 
  (MP e _ _)       -> e 
  (Axiom e _)      -> e 
  (Deducted e _)   -> e 
  (Hypothesis e _) -> e 
  (Incorrect e)    -> e 

withProofLine :: ProofLine -> MarkedExpr -> MarkedExpr
withProofLine pl me = case me of 
  (MP _ i j)       -> MP pl i j
  (Axiom _ i)      -> Axiom pl i
  (Deducted _ i)   -> Deducted pl i
  (Hypothesis _ i) -> Hypothesis pl i
  (Incorrect _)    -> Incorrect pl



isIncorrect :: MarkedExpr -> Bool
isIncorrect (Incorrect _) = True
isIncorrect _ = False

validate :: MarkedExpr -> V.Vector Bool -> MarkedExpr
validate mp@(MP e i j)     vc = if (vc V.! (i - 1)) || (vc V.! (j - 1)) then (MPInc e i j) else mp
validate dd@(Deducted e i) vc = if (vc V.! (i - 1))                     then (DeductedInc e i) else dd
validate e _ = e 
