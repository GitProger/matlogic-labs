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

isAxiom :: ProofLine -> Maybe ProofType
isAxiom line@(ProofLine _ e) = case axiomEnumerate e of 
  n | n > 0 -> Just $ Axiom n
  0 -> Nothing

isHypotize :: ProofLine -> Maybe ProofType
isHypotize pl@(ProofLine (Context c) expr) = for 1 c 
  where for _ [] = Nothing
        for i (hypo:t) | hypo == expr = Just $ Hypothesis i
                       | otherwise    = for (succ i) t

-------------------------------------------------------------------------------
-- select first ok maybe value: --
test :: [Maybe a] -> a -> a
test []          bad = bad
test ((Just ok):t) _ = ok 
test (Nothing:t) bad = test t bad 
--------------------------------------------------------------------------------

findDeduction :: M.Map Context [Indexed ProofLine] -> Indexed ProofLine -> Maybe ProofType
findDeduction extCache (i, line) = if i <= 1 then Nothing else
  let (ProofLine ctx expr) = withSortedCtx . expandCtx $ line
      a = filter (\(j, ProofLine _ e) -> j < i && e == expr) $ (extCache M.! ctx) in
    if a == [] 
      then Nothing
      else let (j, _) = head a in 
            Just $ Deducted j

findModusPonens :: M.Map Context (Twice [Indexed ProofLine]) -> (Int, ProofLine) -> Maybe ProofType
findModusPonens ctxCache (k, line@(ProofLine ctx e)) = if k <= 2 then Nothing else
  let (candidates, implications) = ctxCache M.! ctx in
    takeLastRet (\(j, b) -> -- a := a', b := a' -> b'
                  if j >= k then Nothing else 
                    case find (\(i, a) -> i < k && isModusPonens a b line) candidates of  
                      Just (i, _) -> Just $ MP i j
                      Nothing -> Nothing)
                implications

check :: M.Map Context (Twice [Indexed ProofLine]) -> M.Map Context [Indexed ProofLine] -> Indexed ProofLine -> MarkedExpr
check ctxCache extCache (i, line) = MarkedExpr (line, 
  test [ isAxiom line
       , isHypotize line
       , findDeduction extCache (i, line')
       , findModusPonens ctxCache (i, line') 
       ] Incorrect)
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

simplifyMP :: Expr -> ProofTree -> ProofTree -> ProofTree
simplifyMP e l r = if (axiomEnumerate e /= 0) then (ProofAxiom e) else (ProofMP e l r)

proveDeducts1 :: [Expr] -> ProofTree -> ProofTree
proveDeducts1 []     p = p
proveDeducts1 (h:hs) p = (proveDeducts1 hs (simplifyMP b (ProofHypo h) p)) where (Call Imply _ b) = getProofExpr p -- p = h -> b
                                                                                                                   -- b = mp h p
proveDeducts2 :: Expr -> ProofTree -> ProofTree
proveDeducts2 e (ProofAxiom a) = (simplifyMP (e .-> a) (ProofAxiom a) (ProofAxiom (a .-> e .-> a))) -- "e -> a" = mp a "a -> e -> a" (ax1)
proveDeducts2 e (ProofHypo h)
  | h == e = (simplifyMP (e .-> e) (ProofAxiom (e .-> (e .-> e) .-> e)) -- "e -> e" = mp ax1 e 
              (simplifyMP ((e .-> (e .-> e) .-> e) .-> (e .-> e)) (ProofAxiom (e .-> e .-> e)) -- e = mp ax1
                (ProofAxiom ((e .-> e .-> e) .-> (e .-> (e .-> e) .-> e) .-> (e .-> e)))))     --        ax2
  | otherwise = (simplifyMP (e .-> h) (ProofHypo h) (ProofAxiom (h .-> e .-> h))) -- "e -> h" = mp h "h -> e -> h" (ax1)
proveDeducts2 e mp@(ProofMP c l r)
  | (hasHypothesis e mp) = (simplifyMP (e .-> c) (proveDeducts2 e r)                     --      "e -> c" = mp e r
                            (simplifyMP ((e .-> rc) .-> (e .-> c)) (proveDeducts2 e l)   --      r = mp ax2 lc(l)
                              (ProofAxiom ((e .-> lc) .-> (e .-> rc) .-> (e .-> c)))))   --      ax2 (a = e, b = lc(l), c = c, b->c = rc(r))
  | otherwise = (simplifyMP (e .-> c) mp (ProofAxiom (c .-> e .-> c))) -- "e -> c" = mp c(=center mp@(Proof c _ _)) "c->e->c" (ax1)
 where lc = getProofExpr l
       rc = getProofExpr r

proveDeducts3 :: [Expr] -> ProofTree -> ProofTree
proveDeducts3 []     tree = tree
proveDeducts3 (h:hs) tree 
  | hasHypothesis h tree = (proveDeducts3 hs $! (proveDeducts2 h tree))
  | otherwise            = (proveDeducts3 hs $! (simplifyMP (h .-> c) tree (ProofAxiom (c .-> h .-> c))))
 where c = getProofExpr tree -- center

proveAllDeductionsTF :: Expr -> [Expr] -> [Expr] -> ProofTree -> ProofTree
proveAllDeductionsTF begE falses trues tree = proveDeducts3 trues (proveDeducts1 falses tree)

getImplicationSrcs :: Expr -> ([Expr], Expr)
getImplicationSrcs (Call Imply a b) = (a:l, r) where (l, r) = getImplicationSrcs b
getImplicationSrcs e                = ([], e)

buildImplications :: Expr -> [Expr] -> [Expr] -> (Expr, [Expr], [Expr])
buildImplications e a'@(a:as) b'@(b:bs) 
  | a == b = buildImplications (a .-> e) as bs
buildImplications e a b = (e, a, b)

deductionLCA :: Expr -> Expr -> (Expr, [Expr], [Expr])
deductionLCA x y = 
    let (xPoints, _  ) = getImplicationSrcs x  
        (yPoints, lst) = getImplicationSrcs y 
        (start, esFalse, esTrue) = buildImplications lst (reverse xPoints) (reverse yPoints) in 
      (start, reverse esFalse, esTrue)

buildProofTree :: Int -> [(Int, Expr)] -> [ProofType] -> ProofTree
buildProofTree i ((j, e):es) (pt:pts) = if (i /= j) then buildProofTree i es pts else
  case pt of
    (Axiom _)      -> (ProofAxiom e)
    (Hypothesis _) -> (ProofHypo  e)
    (MP l r)       -> simplifyMP e (buildProofTree l es pts) (buildProofTree r es pts) 
    (Deducted dd)  -> let r = buildProofTree dd es pts
                          (begE, fe, te) = deductionLCA (getProofExpr r) e in
                            proveAllDeductionsTF begE fe te r

main :: IO ()
main = do 
  input <- getContents >>= return . lines
  putStrLn (last input)
  let strs = map (parseProof . alexScanTokens) input
      indexed = zip [1..] strs

      extCache = getExtCache $ zip [1..] $ map (withSortedCtx . expandCtx) strs
      ctxCache = getCtxCache $ map (\(i, p) -> (i, withSortedCtx p)) indexed

      ans = map (check ctxCache extCache) indexed in
    -- putStr . unlines $ zipWith3 (\i orig res -> numbered i $ show $ withProofLine orig res) [1..] strs ans
    let exprs     = map (\(MarkedExpr (ProofLine _ e, _)) -> e) ans
        proofWays = map (\(MarkedExpr (_, pt)) -> pt) ans
        proofTree = buildProofTree (length input) (reverse $ zip [1..] exprs) (reverse proofWays)
        in
      -- putStrLn . unlines . map show . treeToList $ proofTree
      putStrLn . unlines . map (\(e, b) -> if b then show e ++ orig else show e) . treeToListO proofTree $ exprs

-- [a, a1, a2, a3, b, b1, b2, c, c1, c2, c3] = map Variable ["a", "a", "a", "a", "b", "b", "b", "c", "c", "c", "c"]
-- 1  (a->(b->a))
-- 2  ((a->b)->((a->(b->c))->(a->c)))
-- 3  (a->(b->(a&b)))
-- 4  ((a&b)->a)
-- 5  ((a&b)->b)
-- 6  (a->(a|b))
-- 7  (b->(a|b))
-- 8  ((a->c)->((b->c)->((a|b)->c)))
-- 9  ((a->b)->((a->(!b))->(!a)))
-- 10 ((!(!a))->a)
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
