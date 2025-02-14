module Base where
{-# LANGUAGE Strict #-}

import Utils
import Data.List (sort, find, intercalate, elem)
import qualified Data.Map as M
import qualified Data.Set as S

type Indexed a = (Int, a)
type Twice a = (a, a)

data SingleType = IIMpl | ElAnd | ErAnd | IlOr | IrOr | ENot
data DoubleType = EImpl | IAnd
data TripleType = EOr
 
instance Show SingleType where
  show ENot  = "[E!!]"
  show IrOr  = "[Ir|]"
  show IlOr  = "[Il|]"
  show ErAnd = "[Er&]" 
  show ElAnd = "[El&]"
  show IIMpl = "[I->]"
 
instance Show DoubleType where
  show IAnd  = "[I&]"
  show EImpl = "[E->]"
 
instance Show TripleType where
  show EOr = "[E|]"
 
data ProofTree = Ax                     Expr [Expr] 
               | SingleProof SingleType Expr [Expr] ProofTree 
               | DoubleProof DoubleType Expr [Expr] ProofTree ProofTree
               | TripleProof TripleType Expr [Expr] ProofTree ProofTree ProofTree
 
ctxString :: [Expr] -> String
ctxString es = intercalate "," $ map show es

tailStr depth ctx e t = "[" ++ (show depth) ++ "] " ++ (ctxString ctx) ++ "|-" ++ (show e) ++ " " ++ (show t) ++ "\n"

proofStr :: Int -> ProofTree -> String
proofStr depth (Ax e ctx)                     = "[" ++ (show depth) ++ "] " ++ (ctxString ctx) ++ "|-" ++ (show e) ++ " [Ax]\n"
proofStr depth (SingleProof t e ctx p1)       = (proofStr (succ depth) p1) ++ (tailStr depth ctx e t)
proofStr depth (DoubleProof t e ctx p1 p2)    = (proofStr (succ depth) p1) ++ (proofStr (succ depth) p2) ++ (tailStr depth ctx e t)
proofStr depth (TripleProof t e ctx p1 p2 p3) = (proofStr (succ depth) p1) ++ (proofStr (succ depth) p2) ++ (proofStr (succ depth) p3) ++ (tailStr depth ctx e t)

instance Show ProofTree where
  show = proofStr 0

appendCtx :: Expr -> ProofTree -> ProofTree
appendCtx e (Ax expr ctx)                     = (Ax expr (e:ctx))
appendCtx e (SingleProof t expr ctx p1)       = (SingleProof t expr (e:ctx) (appendCtx e p1))
appendCtx e (DoubleProof t expr ctx p1 p2)    = (DoubleProof t expr (e:ctx) (appendCtx e p1) (appendCtx e p2))
appendCtx e (TripleProof t expr ctx p1 p2 p3) = (TripleProof t expr (e:ctx) (appendCtx e p1) (appendCtx e p2) (appendCtx e p3))

varSet :: Expr -> (S.Set Expr)
varSet FalseExpr    = S.empty
varSet (Not e)      = varSet e
varSet (Variable s) = S.singleton (Variable s)
varSet (Call _ a b) = S.union (varSet a) (varSet b)
