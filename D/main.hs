{-# LANGUAGE Strict #-}

import Data.List (sort, find, intercalate, elem)
import qualified Data.Map as M
import qualified Data.Set as S

import Lexer
import Parser
import Utils
import Base
import Helpers

strEvaluation (Variable v) = v ++ ":=T"
strEvaluation (Call _ (Variable v) FalseExpr) = v ++ ":=F"
 
strRefutable :: [Expr] -> String
strRefutable e = "Formula is refutable [" ++ (intercalate "," $ map strEvaluation e) ++ "]"
 
main = getLine >>= (return . parseProof . alexScanTokens) >>= \expr -> 
  let (res, ctx, ok) = proof (S.toList . varSet $ expr) expr [] in 
    if ok then putStr $ show res
          else putStrLn (strRefutable ctx) 
