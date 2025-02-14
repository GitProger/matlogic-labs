module Utils where
{-# LANGUAGE Strict #-}

import           Data.List (intercalate, sort)
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


-------------------------------------------------------------------------------

newtype Context = Context [Expr] deriving (Eq, Ord)
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

-- 'expandCtx' always goes with 'withSortedCtx'
-- expandCtx (ProofLine (Context ctx) (Call Imply a b)) = 
--   expandCtx $ ProofLine (Context $ ctx ++ [a]) b 
-- expandCtx p = p
expandCtx (ProofLine (Context ctx) (Call Imply a b)) = 
  expandCtx $ ProofLine (Context $ a:ctx) b 
expandCtx p = p


-- new version:
data ProofType = MP Int Int | Axiom Int | Deducted Int | Hypothesis Int | Incorrect
instance Show ProofType where
  show (MP i j)       = embrace $ "M.P. " ++ show i ++ ", " ++ show j
  show (Axiom n)      = embrace $ "Ax. sch. " ++ show n
  show (Deducted n)   = embrace $ "Ded. " ++ show n
  show (Hypothesis n) = embrace $ "Hyp. " ++ show n
  show Incorrect      = embrace "Incorrect"

newtype MarkedExpr = MarkedExpr (ProofLine, ProofType)
instance Show MarkedExpr where
  show (MarkedExpr (pl, tp)) = show pl ++ " " ++ show tp

withProofLine :: ProofLine -> MarkedExpr -> MarkedExpr
withProofLine pl (MarkedExpr (_, pt)) = MarkedExpr (pl, pt)

--                        Res   A   B          Expr,     schema num               from
-- data MarkedExpr = MP ProofLine Int Int | Axiom ProofLine Int | Deducted ProofLine Int 
--                                                              | Hypothesis ProofLine Int 
--                                                              | Incorrect ProofLine 
-- instance Show MarkedExpr where
--   show (MP e i j)       = show e ++ " " ++ (embrace $ "M.P. " ++ show i ++ ", " ++ show j)
--   show (Axiom e n)      = show e ++ " " ++ (embrace $ "Ax. sch. " ++ show n)
--   show (Deducted e n)   = show e ++ " " ++ (embrace $ "Ded. " ++ show n)
--   show (Hypothesis e n) = show e ++ " " ++ (embrace $ "Hyp. " ++ show n)
--   show (Incorrect e)    = show e ++ " " ++ (embrace "Incorrect")

-- getProofLine :: MarkedExpr -> ProofLine
-- getProofLine me = case me of 
--   (MP e _ _)       -> e 
--   (Axiom e _)      -> e 
--   (Deducted e _)   -> e 
--   (Hypothesis e _) -> e 
--   (Incorrect e)    -> e 

-- withProofLine :: ProofLine -> MarkedExpr -> MarkedExpr
-- withProofLine pl me = case me of 
--   (MP _ i j)       -> MP pl i j
--   (Axiom _ i)      -> Axiom pl i
--   (Deducted _ i)   -> Deducted pl i
--   (Hypothesis _ i) -> Hypothesis pl i
--   (Incorrect _)    -> Incorrect pl




-- Proof graph
data ProofTree = ProofAxiom Expr | ProofHypo Expr | ProofMP Expr ProofTree ProofTree

instance Show ProofTree where
    show (ProofAxiom e) = show e ++ " [Axiom]\n"
    show (ProofHypo e) = show e ++ " [Hypothes]\n"
    show (ProofMP m l r) = show l ++ show r ++ show m ++ " [MP]\n"

orig = " [from Original proof]"

getProofExpr e = case e of 
  (ProofAxiom e) -> e 
  (ProofHypo e) -> e
  (ProofMP e _ _) -> e
   
hasHypothesis :: Expr -> ProofTree -> Bool
hasHypothesis e (ProofAxiom  _) = False
hasHypothesis e (ProofHypo   h) = (e == h)
hasHypothesis e (ProofMP _ l r) = (hasHypothesis e l) || (hasHypothesis e r)

treeToList' :: ProofTree -> S.Set Expr -> ([Expr], S.Set Expr)
treeToList' (ProofAxiom e)  used = if (S.member e used) then ([], used) else ([e], S.insert e used)
treeToList' (ProofHypo e)   used = if (S.member e used) then ([], used) else ([e], S.insert e used)
treeToList' (ProofMP e l r) used = if (S.member e used) then ([], used) else 
                                                                                let (res1, used1) = treeToList' l used 
                                                                                    (res2, used2) = treeToList' r used1 in 
                                                                                  ((e:res2) ++ res1, S.insert e used2)

treeToList :: ProofTree -> [Expr]
treeToList p = let (l, _) = treeToList' p S.empty in reverse l

mem = S.member

treeToListO' :: ProofTree -> S.Set Expr -> S.Set Expr -> ([(Expr, Bool)], S.Set Expr)
treeToListO' (ProofAxiom e)  was used = if (mem e used) then ([], used) else ([(e, mem e was)], S.insert e used)
treeToListO' (ProofHypo e)   was used = if (mem e used) then ([], used) else ([(e, mem e was)], S.insert e used)
treeToListO' (ProofMP e l r) was used = if (mem e used) then ([], used) else 
                                                                                let (res1, used1) = treeToListO' l was used 
                                                                                    (res2, used2) = treeToListO' r was used1 in 
                                                                                  (((e, mem e was):res2) ++ res1, S.insert e used2)

treeToListO :: ProofTree -> [Expr] -> [(Expr, Bool)]
treeToListO p was = let (l, _) = treeToListO' p (S.fromList was) S.empty in reverse l
