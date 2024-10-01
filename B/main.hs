{-# LANGUAGE Strict #-}

import Lexer
import Parser
import Utils
import Data.Maybe
import Data.List (sort, find, intercalate)
import qualified Data.Map as M

type Indexed a = (Int, a)
type Twice a = (a, a)

verify :: Eq a => [(a, a)] -> Bool
verify = all (uncurry (==))

isImplication (ProofLine _ (Call Imply _ _)) = True
isImplication _ = False 

-------------------------------------------------------------------------------

modusPonens (ProofLine c1 a) (ProofLine c2 (Call Imply a' b)) =
  -- if c1 `cmpUnord` c2 && a == a'
  if c1 == c2 && a == a'
    then Just (ProofLine c1 b)
    else Nothing
modusPonens _ _ = Nothing

-- isX: -----------------------------------------------------------------------
isModusPonens a b res = (Just res) == modusPonens a b

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

findDeduction :: M.Map Context [Indexed ProofLine] -> Indexed ProofLine -> Maybe MarkedExpr
findDeduction extCache (i, line) = if i <= 1 then Nothing else
  let (ProofLine ctx expr) = withSortedCtx $ expandCtx line
      a = filter (\(j, ProofLine _ e) -> j < i && e == expr) $ (extCache M.! ctx) in
    if a == [] 
      then Nothing
      else let (j, _) = head a in 
            Just $ Deducted line j

findModusPonens ctxCache (k, line@(ProofLine ctx e)) = if k <= 2 then Nothing else
  let (candidates, implications) = ctxCache M.! ctx in
    takeLastRet (\(j, b) -> -- a := a', b := a' -> b'
                  if j >= k then Nothing else 
                    case find (\(i, a) -> i < k && isModusPonens a b line) candidates of  
                      Just (i, _) -> Just $ MP line i j
                      Nothing -> Nothing)
                implications

check :: M.Map Context (Twice [Indexed ProofLine]) -> M.Map Context [Indexed ProofLine]
                                                   -> Indexed ProofLine -> MarkedExpr
check ctxCache extCache (i, line) = 
  test [ isAxiom line
       , isHypotize line
       , findDeduction extCache (i, line')
       , findModusPonens ctxCache (i, line') 
       ] $ Incorrect line
      where line' = withSortedCtx line

            --      all                 implications
updatePair :: Twice [Indexed ProofLine] -> Indexed ProofLine -> Twice [Indexed ProofLine]
updatePair (alL, implications) e@(i, pl) = 
  (e:alL, if isImplication pl then e:implications else implications)

withImpl new@(_, p) = ([new], if isImplication p then [new] else [])

getCtxCache :: [Indexed ProofLine] -> M.Map Context (Twice [Indexed ProofLine])
getCtxCache indexed = 
  M.map (double reverse) $ foldl (\mp new@(i, (ProofLine ctx _)) -> 
                                   -- case mp M.!? ctx of 
                                   --   Nothing -> M.insert ctx (updatePair ([], []) new) mp
                                   --   Just old -> M.insert ctx (updatePair old new) mp

                                   -- M.update (\old -> Just $ updatePair old new) ctx mp)
                                   M.insertWith (double2 (++)) ctx (withImpl new) mp
                                 ) M.empty indexed 


getExtCache :: [Indexed ProofLine] -> M.Map Context [Indexed ProofLine]
getExtCache indexed = 
  M.map reverse $ foldl (\mp new@(i, (ProofLine ctx _)) -> M.insertWith (++) ctx [new] mp) M.empty indexed

main :: IO ()
main = do 
  input <- getContents >>= return . lines
  let strs = map (parseProof . alexScanTokens) input
      indexed = zip [1..] strs

      extCache = getExtCache $ zip [1..] $ map (withSortedCtx . expandCtx) strs
      ctxCache = getCtxCache $ map (\(i, p) -> (i, withSortedCtx p)) indexed

      ans = map (check ctxCache extCache) indexed in
    --putStrLn $ intercalate "\n" $ map (\(k, v) -> show k ++ "    ->   " ++ show v) $ M.toAscList extCache
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
