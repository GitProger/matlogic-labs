module Helpers where
{-# LANGUAGE Strict #-}

import Data.List (elem)
import Utils
import Base

--                expr     ctx      proof left, t/f     proof right, t/f       new proof, t/f
proofOperation :: Expr -> [Expr] -> (ProofTree, Bool) -> (ProofTree, Bool) -> (ProofTree, Bool)
proofOperation (Call Or  a b) ctx (pa, True)  _           = ((SingleProof IlOr (a .| b) ctx pa), True)
proofOperation (Call Or  a b) ctx _           (pb, True)  = ((SingleProof IrOr (a .| b) ctx pb), True)
proofOperation (Call And a b) ctx (pa, True)  (pb, True)  = ((DoubleProof IAnd (a .& b) ctx pa pb), True)
proofOperation (Call And a b) ctx _           (pb, False) = ((SingleProof IIMpl ((a .& b) .-> _I_) ctx (DoubleProof EImpl _I_ ((a .& b):ctx) (appendCtx (a .& b) pb) (SingleProof ErAnd b ((a .& b):ctx) (Ax (a .& b) ((a .& b):ctx))))), False)
proofOperation (Call And a b) ctx (pa, False) _           = ((SingleProof IIMpl ((a .& b) .-> _I_) ctx (DoubleProof EImpl _I_ ((a .& b):ctx) (appendCtx (a .& b) pa) (SingleProof ElAnd a ((a .& b):ctx) (Ax (a .& b) ((a .& b):ctx))))), False)
proofOperation (Call Or  a b) ctx (pa, False) (pb, False) = ((SingleProof IIMpl ((a .| b) .-> _I_) ctx (TripleProof EOr   _I_ ((a .| b):ctx)
                                                                                                                                              (DoubleProof EImpl _I_ (a:(a .| b):ctx) (appendCtx a . appendCtx (a .| b) $ pa) (Ax a (a:(a .| b):ctx)))
                                                                                                                                              (DoubleProof EImpl _I_ (b:(a .| b):ctx) (appendCtx b . appendCtx (a .| b) $ pb) (Ax b (b:(a .| b):ctx)))
                                                                                                                                                                                                         (Ax (a .| b) ((a .| b):ctx)))), False)
 
proofOperation (Call Imply a b) ctx _           (pb, True) = ((SingleProof IIMpl (a .-> b) ctx (appendCtx a pb)), True)
proofOperation (Call Imply a b) ctx (pa, False) _          = ((SingleProof IIMpl (a .-> b) ctx
              (DoubleProof EImpl b (a:ctx)
                (SingleProof IIMpl (_I_ .-> b) (a:ctx) (SingleProof ENot b (_I_:a:ctx) (Ax _I_ ((b .-> _I_):_I_:a:ctx))))
                (DoubleProof EImpl _I_ (a:ctx) (appendCtx a pa) (Ax a (a:ctx))))), 
  True)
proofOperation (Call Imply a b) ctx (pa, True) (pb, False) = ((SingleProof IIMpl ((a .-> b) .-> _I_) ctx
              (DoubleProof EImpl _I_ ((a .-> b):ctx)
                (appendCtx (a .-> b) pb)
                (DoubleProof EImpl b ((a .-> b):ctx) (Ax (a .-> b) ((a .-> b):ctx)) (appendCtx (a .-> b) pa)))), 
  False)
 
proofCtx :: [Expr] -> Expr -> (ProofTree, Bool)
proofCtx ctx FalseExpr       = ((SingleProof IIMpl (_I_ .-> _I_) ctx (Ax _I_ (_I_:ctx))), False)
proofCtx ctx (Call oper a b) = proofOperation (Call oper a b) ctx (proofCtx ctx a) (proofCtx ctx b)
proofCtx ctx (Variable s)    = if (Variable s) `elem` ctx
                                then ((Ax ( Variable s         ) ctx), True)
                                else ((Ax ((Variable s) .-> _I_) ctx), False)

rev x = (x .-> _I_)
nn   x = ((rev x) .-> _I_)
ornq x = (x .| (rev x))
ornnq x ctx = (Ax (x .| (rev x) .-> _I_) ctx)

basicProof x ctx = 
  (SingleProof ENot (ornq x) ctx (appendCtx (x .| (rev x) .-> _I_)
    (DoubleProof EImpl _I_ ctx
      (DoubleProof EImpl (nn x) ctx
        (DoubleProof EImpl ((x .| (rev x) .-> _I_) .-> (rev x) .-> _I_) ctx
          (SingleProof IIMpl (((rev x) .-> x .| (rev x)) .-> (x .| (rev x) .-> _I_) .-> (rev x) .-> _I_) ctx 
            (appendCtx ((rev x) .-> x .| (rev x))
                        (SingleProof IIMpl ((x .| (rev x) .-> _I_) .-> (rev x) .-> _I_) ctx 
                          (appendCtx (x .| (rev x) .-> _I_)
                            (SingleProof IIMpl (nn x) ctx (appendCtx (rev x)
                              (DoubleProof EImpl _I_ ctx (ornnq x ctx) (SingleProof IrOr (ornq x) ctx (Ax (rev x) ctx)))))))))
          (SingleProof IIMpl ((rev x) .-> x .| (rev x)) ctx 
            (appendCtx (rev x) (SingleProof IrOr (ornq x) ctx (Ax (rev x) ctx)))))
        (ornnq x ctx))
      (DoubleProof EImpl (rev x) ctx
        (DoubleProof EImpl ((x .| (rev x) .-> _I_) .-> (rev x)) ctx
          (SingleProof IIMpl ((x .-> x .| (rev x)) .-> (x .| (rev x) .-> _I_) .-> (rev x)) ctx 
            (appendCtx (x .-> x .| (rev x)) 
                        (SingleProof IIMpl ((x .| (rev x) .-> _I_) .-> (rev x)) ctx
                          (appendCtx (x .| (rev x) .-> _I_) 
                            (SingleProof IIMpl (rev x) ctx (appendCtx x
                              (DoubleProof EImpl _I_ ctx (ornnq x ctx) (SingleProof IlOr (ornq x) ctx (Ax x ctx)))))))))
          (SingleProof IIMpl (x .-> x .| (rev x)) ctx 
            (appendCtx x (SingleProof IlOr (ornq x) ctx (Ax x ctx)))))
        (ornnq x ctx)))))

--                                     proof      ctx    t/f
proof :: [Expr] -> Expr -> [Expr] -> (ProofTree, [Expr], Bool)
proof [] expr ctx = let (proofRes, ok) = proofCtx ctx expr in (proofRes, ctx, ok)
proof (x:ctxTail) expr ctx | (not okT) = (proofT, ctxT, okT) 
                           | (not okF) = (proofF, ctxF, okF)
                           | otherwise = (TripleProof EOr expr ctx proofT proofF (basicProof x ctx), ctx, True) 
    where
      (proofT, ctxT, okT) = proof ctxTail expr (x:ctx) 
      (proofF, ctxF, okF) = proof ctxTail expr ((rev x):ctx)
