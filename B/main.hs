{-# LANGUAGE Strict #-}

import Lexer
import Parser
import Utils
import Data.List (sort, find)
import qualified Data.Vector as VC

verify :: Eq a => [(a, a)] -> Bool
verify = all (uncurry (==))

modusPonens (ProofLine c1 a) (ProofLine c2 (Call Imply a' b)) =
  -- if c1 `cmpUnord` c2 && a == a'
  if c1 == c2 && a == a'
    then Just (ProofLine c1 b)
    else Nothing
modusPonens _ _ = Nothing

-------------------------------------------------------------------------------
-- deduction variants: --------------------------------------------------------
-- deduct (ProofLine (Context (c1:cn)) e) = ProofLine (Context cn) $ Call Imply c1 e
-- deduct e = e

-- cabBeDeducted from to
--   | df == to   = True
--   | df == from = False
--   | otherwise  = cabBeDeducted df to
--   where df = deduct from

-- cabBeDeductedExt a b = cabBeDeducted a b || cabBeDeducted b a

-- cabBeDeducted' from to = 
--   let ProofLine c1 e1 = expandCtx from
--       ProofLine c2 e2 = expandCtx to in 
--     e1 == e2 && c1 `cmpUnord` c2

cabBeDeductedFast cache i j = (cache VC.! (i - 1)) == (cache VC.! (j - 1))

-- isX: -----------------------------------------------------------------------
isModusPonens p1 p2 (ProofLine c' e') = case modusPonens p1 p2 of 
  Just (ProofLine c e) -> e == e' && c == c' -- c `cmpUnord` c'
  Nothing -> False

isAxiom :: ProofLine -> Maybe MarkedExpr
isAxiom line@(ProofLine _ e) = case axiomEnumerate e of 
  n | n > 0 -> Just $ Axiom line n
  0 -> Nothing

isHypotize :: ProofLine -> Maybe MarkedExpr
isHypotize pl@(ProofLine (Context c) expr) = for 1 c 
  where for _ [] = Nothing
        for i (hypo:t) | hypo == expr = Just $ Hypothesis pl i 
                       | otherwise    = for (succ i) t

-------------------------------------------------------------------------------
-- select first ok maybe value: --
test :: [Maybe a] -> a -> a
test []          bad = bad
test ((Just ok):t) _ = ok 
test (Nothing:t) bad = test t bad 
--------------------------------------------------------------------------------

findDeduction cache entire (i, line) = if i <= 1 then Nothing else
  takeLastRet (\(j, prev) -> 
                -- if cabBeDeducted' prev line
                if cabBeDeductedFast cache j i
                  then Just $ Deducted line j
                  else Nothing)
              $ takeWhile ((<i) . fst) entire

findModusPonens entire (i, line@(ProofLine ctx e)) = if i <= 2 then Nothing else
  let candidates = filter ((== ctx) . getContext . snd) -- (cmpUnord ctx)
                        $ takeWhile ((<i) . fst) entire
      isImplication (ProofLine _ (Call Imply _ _)) = True
      isImplication _ = False 

      -- a, a -> b |= b ; look for (->)
      implications = filter (isImplication . snd) candidates
  in
    takeLastRet (\(j, b) -> -- a := a', b := a' -> b'
                  case find (\(i, a) -> isModusPonens a b line) candidates of  
                    Just (i, _) -> Just $ MP line i j
                    Nothing -> Nothing)
                implications

check :: [(Int, ProofLine)] -> VC.Vector ProofLine -> (Int, ProofLine) -> MarkedExpr
check entire cache (i, line) = 
  test [ isAxiom line
       , isHypotize line
       , findDeduction cache entire' (i, line')
       , findModusPonens entire' (i, line') 
       ] $ Incorrect line 
      where entire' = map (\(i, p) -> (i, withSortedCtx p)) entire
            line' = withSortedCtx line

main :: IO ()
main = getContents >>= return . map (parseProof . alexScanTokens) . lines >>= \strs ->
  let indexed = zip [1..] strs
      cache = VC.fromList $ map (withSortedCtx . expandCtx) strs
      ans = map (check indexed cache) indexed in
    putStr . unlines $ zipWith3 (\i orig res -> numbered i $ show $ withProofLine orig res) [1..] strs ans


axiomEnumerate :: Expr -> Int
axiomEnumerate e = case e of 
  (Call Imply a1 (Call Imply b a2)) | verify [(a1, a2)] -> 1
  (Call Imply (Call Imply a1 b1) (Call Imply (Call Imply a2 (Call Imply b2 c1)) (Call Imply a3 c2))) | verify [ (a1, a2)  
                                                                                                              , (a2, a3)
                                                                                                              , (b1, b2)
                                                                                                              , (c1, c2) ] -> 2
  (Call Imply a1 (Call Imply b1 (Call And a2 b2))) | verify [ (a1, a2)
                                                            , (b1, b2) ] -> 3
  (Call Imply (Call And a1 b) a2) | verify [(a1, a2)] -> 4
  (Call Imply (Call And a b1) b2) | verify [(b1, b2)] -> 5
  (Call Imply a1 (Call Or a2 b))  | verify [(a1, a2)] -> 6
  (Call Imply b1 (Call Or a b2))  | verify [(b1, b2)] -> 7
  (Call Imply (Call Imply a1 c1) (Call Imply (Call Imply b1 c2) (Call Imply (Call Or a2 b2) c3))) | verify [ (a1, a2)
                                                                                                           , (b1, b2)
                                                                                                           , (c1, c2)
                                                                                                           , (c2, c3) ] -> 8
  (Call Imply (Call Imply a1 b1) (Call Imply (Call Imply a2 (Not b2)) (Not a3))) | verify [ (a1, a2)
                                                                                          , (a2, a3)
                                                                                          , (b1, b2) ] -> 9
  (Call Imply (Not (Not a1)) a2) | verify [(a1, a2)] -> 10
  otherwise -> 0
