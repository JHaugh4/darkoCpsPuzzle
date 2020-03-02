module Main where

import Control.Monad.State

type Label  = String
type Var    = String
data Const  = Tru | Fls
data PrimOp = Add | Sub | Mul

data Term = Var Var
          | Abs Var Term
          | App Term Term
          | Const Const
          | PrimApp PrimOp [Term]
          | Record [(Label, Term)]

toCPS_DanvyFilinski_HigherOrder_US :: Term -> (Term -> Term) -> Term
toCPS_DanvyFilinski_HigherOrder_US t = (fst (runState (cc t) 1))
  where
    fresh :: (Int -> a) -> State Int a
    fresh f = do n <- get; put (n+1); return (f n)
    freshVarCont :: State Int Var
    freshVarCont = fresh (\n -> "$k" ++ show n)
    freshVarRes :: State Int Var
    freshVarRes = fresh (\n -> "$v" ++ show n)
    cc :: Term -> State Int ((Term -> Term) -> Term)
    cc t = case t of
      Var x ->
        return (\kappa -> kappa (Var x))
      Abs x t2 -> do
        k <- freshVarCont
        t2' <- cc t2
        return (\kappa -> kappa (Abs x (Abs k (t2'
                 (\m -> App (Var k) m)))))
      App t1 t2 -> do
        a <- freshVarRes
        t1' <- cc t1
        t2' <- cc t2
        return (\kappa -> t1'
                 (\m -> t2'
                   (\n -> App (App m n)
                              (Abs a (kappa (Var a))))))
      Const c ->
        return (\kappa -> kappa (Const c))
      PrimApp p [t1] -> do
        t1' <- cc t1
        return (\kappa -> t1'
                 (\v1 -> kappa (PrimApp p [v1])))
      PrimApp p [t1, t2] -> do
        t1' <- cc t1
        t2' <- cc t2
        return (\kappa -> t1'
                 (\v1 -> t2'
                   (\v2 -> kappa (PrimApp p [v1, v2]))))

answer :: [(Term -> Term) -> Term] -> ((Term -> Term) -> Term)
answer []     = error "Not good"
answer (t:ts) = \kappa -> t (answer' kappa ts [])

freshLabels :: [Label]
freshLabels = fmap show [ 0.. ]

answer' :: (Term -> Term) -> [(Term -> Term) -> Term] -> [Term] -> Term -> Term
answer' kappa [] vs     = \v -> kappa (Record $ zip freshLabels (vs ++ [v]))
answer' kappa (t:ts) vs = \v -> t (answer' kappa ts (vs ++ [v]))
  
main :: IO ()
main = do
  putStrLn "hello world"
