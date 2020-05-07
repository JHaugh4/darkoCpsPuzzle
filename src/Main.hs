module Main where

import Control.Monad.State

type Label  = String
type Var    = String
data Const  = Tru | Fls | IntConst Integer | CharConst Char | Unit deriving (Eq, Show)
data PrimOp = Add | Sub | Mul deriving (Eq, Show)

data Term = Var Var
          | Abs Var Term
          | App Term Term
          | Const Const
          | PrimApp PrimOp [Term]
          | Record [(Label, Term)]
          deriving (Eq, Show)

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
      PrimApp p ts -> do
        ts' <- traverse cc ts
        -- General version
        -- return $ answerGeneral (PrimApp p) ts'
        return $ answerPrimApp p ts'
      -- PrimApp p [t1] -> do
      --   t1' <- cc t1
      --   return (\kappa -> t1'
      --            (\v1 -> kappa (PrimApp p [v1])))
      -- PrimApp p [t1, t2] -> do
      --   t1' <- cc t1
      --   t2' <- cc t2
      --   return (\kappa -> t1'
      --            (\v1 -> t2'
      --              (\v2 -> kappa (PrimApp p [v1, v2]))))
      Record rs -> do
        -- Get the labels
        let ls = fmap fst rs
        -- Get the terms
        let ts = fmap snd rs
        -- CPS each term
        ts' <- traverse cc ts
        -- General verions
        -- return $ answerGeneral (\vs -> Record $ zip ls vs) ts'
        -- Call answer on the list of labels and CPS'd terms
        return $ answer (zip ls ts')

{-
  Accepts the list of records where the term has already been cpsd.
  It then takes off the first record and generates a lambda with the kappa
  continuation that will be used in the base case of answer'. It then uses
  the cpsd term to collapse the call to answer'. The call to answer' is given
  its final continuation the rest of the cpsd records the initial label and empty
  list to collect the values.
-}
answer :: [(Label, (Term -> Term) -> Term)] -> ((Term -> Term) -> Term)
answer []           = error "empty list"
--                    This is the final continuation that is called at the end of the computation
--                    has to be carried through the computation
--                    Add l to the list of labels cannot add anything to list of terms yet as it hasn't been calculated yet
answer ((l, t):lts) = \kappa -> t (answer' kappa lts [l] [])

{-
  This function does the tricky job of seemingly creating nested lambdas at runtime.
  The trick is to call cpsd term t on the recursive call. Notice that I do not give the last
  term argument to the recursive call thus it has type Term -> Term which is what t needs to return
  a term. Once I saw that trick the rest was relatively simple, loop through the records and add their
  return values v and labels l to list as you go along. Then when you reach the end of the records
  use the continuation kappa to do the final collapse and hand the labels and values to Record.
-}
answer' :: (Term -> Term) -> [(Label, (Term -> Term) -> Term)] -> [Label] -> [Term] -> Term -> Term
-- Base case use kappa to produce the final term from the reconstructed record
-- ls and vs are carried throughout the computation to keep track of each records term
-- Add the last v to the end of the list and use kappa to produce the final term
answer' kappa [] ls vs           = \v -> kappa (Record $ zip ls (vs ++ [v]))
-- For each element in the list of records produce a lambda with type Term -> Term
-- Then use the given continuation t to collapse the recursive call to answer'
-- Note that answer' is partially applied and returns Term -> Term which when t is applied to that
-- produces Term which then makes the entire lambda Term -> Term just as we needed.
-- This is why this works at each level t is collapsing the recursive call until you get to the base case
-- and kappa does the final collapse.
answer' kappa ((l, t):lts) ls vs = \v -> t (answer' kappa lts (ls ++ [l]) (vs ++ [v]))

answerPrimApp :: PrimOp -> [(Term -> Term) -> Term] -> ((Term -> Term) -> Term)
answerPrimApp pop [] = error "empty list"
answerPrimApp pop (t:ts) = \kappa -> t (answerPrimApp' pop kappa ts [])

answerPrimApp' :: PrimOp -> (Term -> Term) -> [(Term -> Term) -> Term] -> [Term] -> Term -> Term
answerPrimApp' pop kappa [] vs = \v -> kappa (PrimApp pop (vs ++ [v]))
answerPrimApp' pop kappa (t:ts) vs = \v -> t (answerPrimApp' pop kappa ts (vs ++ [v]))

-- Fully general
answerGeneral :: ([a] -> a) -> [(a -> a) -> a] -> ((a -> a) -> a)
answerGeneral constr [] = error "empty list"
answerGeneral constr (t:ts) = \kappa -> t (answerGeneral' constr kappa ts [])

answerGeneral' :: ([a] -> a) -> (a -> a) -> [(a -> a) -> a] -> [a] -> a -> a
answerGeneral' constr kappa [] vs = \v -> kappa (constr (vs ++ [v]))
answerGeneral' constr kappa (t:ts) vs = \v -> t (answerGeneral' constr kappa ts (vs ++ [v]))

-- answerGeneralFold :: ([Term] -> Term) -> [(Term -> Term) -> Term] -> ((Term -> Term) -> Term)
-- answerGeneralFold constr (t:ts) = \kappa -> t (answerGeneralFold' constr kappa ts [])

-- answerGeneralFold' :: ([Term] -> Term) -> (Term -> Term) -> [(Term -> Term) -> Term] -> [Term] -> Term -> Term
-- answerGeneralFold' constr kappa ts vs v = foldr (\t xs -> t $ answerGeneralFold' constr kappa xs (vs ++ [v])) (\v1 -> kappa . constr $ vs ++ [v1])

testTerm1 :: Term
testTerm1 = PrimApp Add [ Const $ IntConst 1, Const $ IntConst 2 ]

testTerm2 :: Term
testTerm2 = PrimApp Add [ App (Abs "x" (Const $ IntConst 1)) (Const Tru), Const $ IntConst 2 ]

testTerm3 :: Term
testTerm3 = Record [("1", App (Abs "x" (Const $ IntConst 1)) (Const Tru)), ("2", Const $ IntConst 2), ("3", testTerm2)]

main :: IO ()
main = do
  let f = flip toCPS_DanvyFilinski_HigherOrder_US $ id
  putStrLn "Record Examples"
  let recAns1 = f testTerm3
  putStrLn $ "Term = " ++ show testTerm3 ++ "\nCPS Term = " ++ show recAns1

  let primAns1 = f testTerm1
  let primAns2 = f testTerm2

  putStrLn $ "Term = " ++ show testTerm1 ++ "\nCPS Term = " ++ show primAns1
  putStrLn $ "Term = " ++ show testTerm1 ++ "\nCPS Term = " ++ show primAns1