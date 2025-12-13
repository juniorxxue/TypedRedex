{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Main (main) where

import Control.Applicative (empty)
import Shallow.Core.Kanren
import Shallow.Core.Internal.Logic (Logic (Ground), LogicType (..))
import Shallow.Interpreters.SubstKanren (runSubstKanren, takeS, Stream)
import Shallow.Utils.Type (quote0, quote1, quote2, quote3)

-- PCF (Programming Computable Functions) with fixpoints
-- Small-step call-by-value operational semantics

-- Natural numbers for de Bruijn indices
data Nat = Z | S Nat deriving (Eq, Show)

instance LogicType Nat where
  data Reified Nat var = ZR | SR (Logic Nat var)

  project Z = ZR
  project (S n) = SR (Ground $ project n)

  reify ZR = Just Z
  reify (SR (Ground n)) = S <$> reify n
  reify _ = Nothing

  quote ZR = quote0 "Z" ZR
  quote (SR n) = quote1 "S" SR n

  unifyVal _ ZR ZR = pure ()
  unifyVal unif (SR x) (SR y) = unif x y
  unifyVal _ _ _ = empty

  derefVal _ ZR = pure Z
  derefVal deref (SR n) = S <$> deref n

zro :: Logic Nat var
zro = Ground ZR

suc :: Logic Nat var -> Logic Nat var
suc = Ground . SR

-- PCF Terms
data Tm
  = Var Nat            -- x
  | Lam Tm             -- λx.e
  | App Tm Tm          -- e₁ e₂
  | Zero               -- 0
  | Succ Tm            -- succ(e)
  | Pred Tm            -- pred(e)
  | Ifz Tm Tm Tm       -- ifz(e, e₁, e₂): if e=0 then e₁ else e₂
  | Fix Tm             -- fix e (fixpoint combinator)
  deriving (Eq, Show)

instance LogicType Tm where
  data Reified Tm var
    = VarR (Logic Nat var)
    | LamR (Logic Tm var)
    | AppR (Logic Tm var) (Logic Tm var)
    | ZeroR
    | SuccR (Logic Tm var)
    | PredR (Logic Tm var)
    | IfzR (Logic Tm var) (Logic Tm var) (Logic Tm var)
    | FixR (Logic Tm var)

  project (Var n) = VarR (Ground $ project n)
  project (Lam b) = LamR (Ground $ project b)
  project (App f a) = AppR (Ground $ project f) (Ground $ project a)
  project Zero = ZeroR
  project (Succ e) = SuccR (Ground $ project e)
  project (Pred e) = PredR (Ground $ project e)
  project (Ifz e e1 e2) = IfzR (Ground $ project e) (Ground $ project e1) (Ground $ project e2)
  project (Fix e) = FixR (Ground $ project e)

  reify (VarR (Ground n)) = Var <$> reify n
  reify (LamR (Ground b)) = Lam <$> reify b
  reify (AppR (Ground f) (Ground a)) = App <$> reify f <*> reify a
  reify ZeroR = Just Zero
  reify (SuccR (Ground e)) = Succ <$> reify e
  reify (PredR (Ground e)) = Pred <$> reify e
  reify (IfzR (Ground e) (Ground e1) (Ground e2)) = Ifz <$> reify e <*> reify e1 <*> reify e2
  reify (FixR (Ground e)) = Fix <$> reify e
  reify _ = Nothing

  quote (VarR n) = quote1 "Var" VarR n
  quote (LamR b) = quote1 "Lam" LamR b
  quote (AppR f a) = quote2 "App" AppR f a
  quote ZeroR = quote0 "Zero" ZeroR
  quote (SuccR e) = quote1 "Succ" SuccR e
  quote (PredR e) = quote1 "Pred" PredR e
  quote (IfzR e e1 e2) = quote3 "Ifz" IfzR e e1 e2
  quote (FixR e) = quote1 "Fix" FixR e

  unifyVal unif (VarR n) (VarR n') = unif n n'
  unifyVal unif (LamR b) (LamR b') = unif b b'
  unifyVal unif (AppR f a) (AppR f' a') = unif f f' *> unif a a'
  unifyVal _ ZeroR ZeroR = pure ()
  unifyVal unif (SuccR e) (SuccR e') = unif e e'
  unifyVal unif (PredR e) (PredR e') = unif e e'
  unifyVal unif (IfzR e e1 e2) (IfzR e' e1' e2') = unif e e' *> unif e1 e1' *> unif e2 e2'
  unifyVal unif (FixR e) (FixR e') = unif e e'
  unifyVal _ _ _ = empty

  derefVal deref (VarR n) = Var <$> deref n
  derefVal deref (LamR b) = Lam <$> deref b
  derefVal deref (AppR f a) = App <$> deref f <*> deref a
  derefVal _ ZeroR = pure Zero
  derefVal deref (SuccR e) = Succ <$> deref e
  derefVal deref (PredR e) = Pred <$> deref e
  derefVal deref (IfzR e e1 e2) = Ifz <$> deref e <*> deref e1 <*> deref e2
  derefVal deref (FixR e) = Fix <$> deref e

var :: Logic Nat var -> Logic Tm var
var = Ground . VarR

lam :: Logic Tm var -> Logic Tm var
lam = Ground . LamR

app :: Logic Tm var -> Logic Tm var -> Logic Tm var
app f a = Ground $ AppR f a

zero :: Logic Tm var
zero = Ground ZeroR

succTm :: Logic Tm var -> Logic Tm var
succTm = Ground . SuccR

predTm :: Logic Tm var -> Logic Tm var
predTm = Ground . PredR

ifz :: Logic Tm var -> Logic Tm var -> Logic Tm var -> Logic Tm var
ifz e e1 e2 = Ground $ IfzR e e1 e2

fix :: Logic Tm var -> Logic Tm var
fix = Ground . FixR

-- Value predicate: lambdas, zero, and successors of values are values
value :: (Kanren rel) => L Tm rel -> Relation rel
value = relation "value" $ \t ->
  conde
    [ fresh $ \b -> t <=> lam b
    , t <=> zero
    , fresh $ \v -> do
        t <=> succTm v
        call $ value v
        pure ()
    ]

-- Naive substitution (not capture-avoiding)
subst0 :: (Kanren rel) => L Tm rel -> L Tm rel -> L Tm rel -> Relation rel
subst0 = relation3 "subst0" $ \body arg out ->
  conde
    [ -- Lambda: don't substitute under binder
      fresh $ \b -> do
        body <=> lam b
        out <=> lam b
        pure ()
    , -- Variable
      fresh2 $ \n n' -> do
        body <=> var n
        conde
          [ do
              n <=> zro
              out <=> arg
              pure ()
          , do
              n <=> suc n'
              out <=> var n'
              pure ()
          ]
        pure ()
    , -- Application
      fresh4 $ \f a f' a' -> do
        body <=> app f a
        call $ subst0 f arg f'
        call $ subst0 a arg a'
        out <=> app f' a'
        pure ()
    , -- Zero
      do
        body <=> zero
        out <=> zero
        pure ()
    , -- Succ
      fresh2 $ \e e' -> do
        body <=> succTm e
        call $ subst0 e arg e'
        out <=> succTm e'
        pure ()
    , -- Pred
      fresh2 $ \e e' -> do
        body <=> predTm e
        call $ subst0 e arg e'
        out <=> predTm e'
        pure ()
    , -- Ifz
      fresh3 $ \e e1 e2 -> fresh3 $ \e' e1' e2' -> do
        body <=> ifz e e1 e2
        call $ subst0 e arg e'
        call $ subst0 e1 arg e1'
        call $ subst0 e2 arg e2'
        out <=> ifz e' e1' e2'
        pure ()
    , -- Fix
      fresh2 $ \e e' -> do
        body <=> fix e
        call $ subst0 e arg e'
        out <=> fix e'
        pure ()
    ]

-- Small-step operational semantics
-- Beta reduction
stepBeta :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
stepBeta = relation2 "step_beta" $ \t t' -> fresh2 $ \b v -> do
  t <=> app (lam b) v
  call $ value v
  call $ subst0 b v t'
  pure ()

-- App left
stepAppL :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
stepAppL = relation2 "step_appL" $ \t t' -> fresh3 $ \e1 e1' e2 -> do
  t <=> app e1 e2
  call $ step e1 e1'
  t' <=> app e1' e2
  pure ()

-- App right
stepAppR :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
stepAppR = relation2 "step_appR" $ \t t' -> fresh3 $ \v e2 e2' -> do
  t <=> app v e2
  call $ value v
  call $ step e2 e2'
  t' <=> app v e2'
  pure ()

-- Succ step
stepSucc :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
stepSucc = relation2 "step_succ" $ \t t' -> fresh2 $ \e e' -> do
  t <=> succTm e
  call $ step e e'
  t' <=> succTm e'
  pure ()

-- Pred of zero
stepPredZero :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
stepPredZero = relation2 "step_pred_zero" $ \t t' -> do
  t <=> predTm zero
  t' <=> zero
  pure ()

-- Pred of successor
stepPredSucc :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
stepPredSucc = relation2 "step_pred_succ" $ \t t' -> fresh $ \v -> do
  t <=> predTm (succTm v)
  call $ value v
  t' <=> v
  pure ()

-- Pred congruence
stepPred :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
stepPred = relation2 "step_pred" $ \t t' -> fresh2 $ \e e' -> do
  t <=> predTm e
  call $ step e e'
  t' <=> predTm e'
  pure ()

-- Ifz when zero
stepIfzZero :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
stepIfzZero = relation2 "step_ifz_zero" $ \t t' -> fresh2 $ \e1 e2 -> do
  t <=> ifz zero e1 e2
  t' <=> e1
  pure ()

-- Ifz when successor
stepIfzSucc :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
stepIfzSucc = relation2 "step_ifz_succ" $ \t t' -> fresh3 $ \v e1 e2 -> do
  t <=> ifz (succTm v) e1 e2
  call $ value v
  t' <=> e2
  pure ()

-- Ifz congruence
stepIfzCong :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
stepIfzCong = relation2 "step_ifz_cong" $ \t t' -> fresh4 $ \e e' e1 e2 -> do
  t <=> ifz e e1 e2
  call $ step e e'
  t' <=> ifz e' e1 e2
  pure ()

-- Fix unrolling: fix e → e (fix e)
stepFix :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
stepFix = relation2 "step_fix" $ \t t' -> fresh $ \e -> do
  t <=> fix e
  t' <=> app e (fix e)
  pure ()

-- Combined step relation
step :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
step = relation2 "step" $ \t t' ->
  conde
    [ call $ stepBeta t t'
    , call $ stepAppL t t'
    , call $ stepAppR t t'
    , call $ stepSucc t t'
    , call $ stepPredZero t t'
    , call $ stepPredSucc t t'
    , call $ stepPred t t'
    , call $ stepIfzZero t t'
    , call $ stepIfzSucc t t'
    , call $ stepIfzCong t t'
    , call $ stepFix t t'
    ]

-- Run step in mode (I,O)
stepIO :: Tm -> Stream Tm
stepIO t0 = runSubstKanren $ fresh $ \t' -> do
  _ <- embed $ step (Ground $ project t0) t'
  eval t'

main :: IO ()
main = do
  putStrLn "=== PCF Small-Step Semantics with Fixpoints ==="
  putStrLn ""

  -- Example 1: pred(succ(0)) → 0
  let ex1 = Pred (Succ Zero)
  putStrLn "Step: pred(succ(0))"
  print $ takeS 3 (stepIO ex1)
  putStrLn ""

  -- Example 2: ifz(0, succ(0), pred(0)) → succ(0)
  let ex2 = Ifz Zero (Succ Zero) (Pred Zero)
  putStrLn "Step: ifz(0, succ(0), pred(0))"
  print $ takeS 1 (stepIO ex2)
  putStrLn ""

  -- Example 3: Application (λx.x) 0 → 0
  let ex3 = App (Lam (Var Z)) Zero
  putStrLn "Step: (λx.x) 0"
  print $ takeS 1 (stepIO ex3)
  putStrLn ""

  -- Example 4: Fix unrolling
  -- fix (λf. λx. ifz(x, 0, succ(f (pred x))))
  -- This is a contrived fixpoint example
  let fixBody = Lam (Lam (Ifz (Var Z) Zero (Succ (App (Var (S Z)) (Pred (Var Z))))))
  let ex4 = Fix fixBody
  putStrLn "Step: fix (λf. λx. ifz(x, 0, succ(f (pred x))))"
  print $ takeS 1 (stepIO ex4)
  putStrLn ""

  -- Example 5: Complex evaluation
  -- (λx. succ(succ(x))) (pred(succ(0)))
  let ex5 = App (Lam (Succ (Succ (Var Z)))) (Pred (Succ Zero))
  putStrLn "Multi-step: (λx. succ(succ(x))) (pred(succ(0)))"
  print $ takeS 5 (stepIO ex5)
