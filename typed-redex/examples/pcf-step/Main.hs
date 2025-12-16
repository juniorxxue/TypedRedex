{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Main (main) where

import Control.Applicative (empty)
import TypedRedex.Core.Redex
import TypedRedex.Core.Internal.Logic (Logic (Ground), LogicType (..))
import TypedRedex.Interpreters.SubstRedex (runSubstRedex, takeS, Stream)
import TypedRedex.Utils.Type (quote0, quote1, quote2, quote3)

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
value :: (Redex rel) => L Tm rel -> Relation rel
value = relation "value" $ \t ->
  conde
    [ fresh $ \b -> t <=> lam b
    , t <=> zero
    , fresh $ \v -> do
        t <=> succTm v
        call (value v)
    ]

-- Naive substitution (not capture-avoiding)
-- subst0 body arg out means [arg/0]body = out

-- Lambda: don't substitute under binder
subst0Lam :: (Redex rel) => L Tm rel -> L Tm rel -> L Tm rel -> Relation rel
subst0Lam = rule3 "subst0-lam" $ \concl ->
  fresh2 $ \b arg ->
    concl (lam b) arg (lam b)

-- Variable at index 0: replace with arg
subst0Var0 :: (Redex rel) => L Tm rel -> L Tm rel -> L Tm rel -> Relation rel
subst0Var0 = rule3 "subst0-var0" $ \concl ->
  fresh $ \arg ->
    concl (var zro) arg arg

-- Variable at index n+1: decrement to n
subst0VarS :: (Redex rel) => L Tm rel -> L Tm rel -> L Tm rel -> Relation rel
subst0VarS = rule3 "subst0-varS" $ \concl ->
  fresh2 $ \n' arg ->
    concl (var (suc n')) arg (var n')

-- Application
subst0App :: (Redex rel) => L Tm rel -> L Tm rel -> L Tm rel -> Relation rel
subst0App = rule3 "subst0-app" $ \concl ->
  fresh5 $ \f a arg f' a' -> do
    concl (app f a) arg (app f' a')
    call (subst0 f arg f')
    call (subst0 a arg a')

-- Zero
subst0Zero :: (Redex rel) => L Tm rel -> L Tm rel -> L Tm rel -> Relation rel
subst0Zero = rule3 "subst0-zero" $ \concl ->
  fresh $ \arg ->
    concl zero arg zero

-- Succ
subst0Succ :: (Redex rel) => L Tm rel -> L Tm rel -> L Tm rel -> Relation rel
subst0Succ = rule3 "subst0-succ" $ \concl ->
  fresh3 $ \e arg e' -> do
    concl (succTm e) arg (succTm e')
    call (subst0 e arg e')

-- Pred
subst0Pred :: (Redex rel) => L Tm rel -> L Tm rel -> L Tm rel -> Relation rel
subst0Pred = rule3 "subst0-pred" $ \concl ->
  fresh3 $ \e arg e' -> do
    concl (predTm e) arg (predTm e')
    call (subst0 e arg e')

-- Ifz
subst0Ifz :: (Redex rel) => L Tm rel -> L Tm rel -> L Tm rel -> Relation rel
subst0Ifz = rule3 "subst0-ifz" $ \concl ->
  fresh4 $ \e e1 e2 arg -> fresh3 $ \e' e1' e2' -> do
    concl (ifz e e1 e2) arg (ifz e' e1' e2')
    call (subst0 e arg e')
    call (subst0 e1 arg e1')
    call (subst0 e2 arg e2')

-- Fix
subst0Fix :: (Redex rel) => L Tm rel -> L Tm rel -> L Tm rel -> Relation rel
subst0Fix = rule3 "subst0-fix" $ \concl ->
  fresh3 $ \e arg e' -> do
    concl (fix e) arg (fix e')
    call (subst0 e arg e')

-- Combined substitution relation
subst0 :: (Redex rel) => L Tm rel -> L Tm rel -> L Tm rel -> Relation rel
subst0 = rules3 "subst0"
  [ subst0Lam
  , subst0Var0
  , subst0VarS
  , subst0App
  , subst0Zero
  , subst0Succ
  , subst0Pred
  , subst0Ifz
  , subst0Fix
  ]

-- Small-step operational semantics
-- Beta reduction
stepBeta :: (Redex rel) => L Tm rel -> L Tm rel -> Relation rel
stepBeta = rule2 "β" $ \concl ->
  fresh3 $ \body v e' -> do
    concl (app (lam body) v) e'
    call (value v)
    call (subst0 body v e')

-- App left
stepAppL :: (Redex rel) => L Tm rel -> L Tm rel -> Relation rel
stepAppL = rule2 "app-L" $ \concl ->
  fresh3 $ \e1 e1' e2 -> do
    concl (app e1 e2) (app e1' e2)
    call (step e1 e1')

-- App right
stepAppR :: (Redex rel) => L Tm rel -> L Tm rel -> Relation rel
stepAppR = rule2 "app-R" $ \concl ->
  fresh3 $ \v e2 e2' -> do
    concl (app v e2) (app v e2')
    call (value v)
    call (step e2 e2')

-- Succ step
stepSucc :: (Redex rel) => L Tm rel -> L Tm rel -> Relation rel
stepSucc = rule2 "succ" $ \concl ->
  fresh2 $ \e e' -> do
    concl (succTm e) (succTm e')
    call (step e e')

-- Pred of zero
stepPredZero :: (Redex rel) => L Tm rel -> L Tm rel -> Relation rel
stepPredZero = axiom2 "pred-zero" (predTm zero) zero

-- Pred of successor
stepPredSucc :: (Redex rel) => L Tm rel -> L Tm rel -> Relation rel
stepPredSucc = rule2 "pred-succ" $ \concl ->
  fresh $ \v -> do
    concl (predTm (succTm v)) v
    call (value v)

-- Pred congruence
stepPred :: (Redex rel) => L Tm rel -> L Tm rel -> Relation rel
stepPred = rule2 "pred" $ \concl ->
  fresh2 $ \e e' -> do
    concl (predTm e) (predTm e')
    call (step e e')

-- Ifz when zero
stepIfzZero :: (Redex rel) => L Tm rel -> L Tm rel -> Relation rel
stepIfzZero = rule2 "ifz-zero" $ \concl ->
  fresh2 $ \e1 e2 ->
    concl (ifz zero e1 e2) e1

-- Ifz when successor
stepIfzSucc :: (Redex rel) => L Tm rel -> L Tm rel -> Relation rel
stepIfzSucc = rule2 "ifz-succ" $ \concl ->
  fresh3 $ \v e1 e2 -> do
    concl (ifz (succTm v) e1 e2) e2
    call (value v)

-- Ifz congruence
stepIfzCong :: (Redex rel) => L Tm rel -> L Tm rel -> Relation rel
stepIfzCong = rule2 "ifz" $ \concl ->
  fresh4 $ \e e' e1 e2 -> do
    concl (ifz e e1 e2) (ifz e' e1 e2)
    call (step e e')

-- Fix unrolling: fix e → e (fix e)
stepFix :: (Redex rel) => L Tm rel -> L Tm rel -> Relation rel
stepFix = rule2 "fix" $ \concl ->
  fresh $ \e ->
    concl (fix e) (app e (fix e))

-- Combined step relation
step :: (Redex rel) => L Tm rel -> L Tm rel -> Relation rel
step = rules2 "step"
  [ stepBeta
  , stepAppL
  , stepAppR
  , stepSucc
  , stepPredZero
  , stepPredSucc
  , stepPred
  , stepIfzZero
  , stepIfzSucc
  , stepIfzCong
  , stepFix
  ]

-- Run step in mode (I,O)
stepIO :: Tm -> Stream Tm
stepIO t0 = runSubstRedex $ fresh $ \t' -> do
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
