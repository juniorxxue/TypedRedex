{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Main (main) where

import Control.Applicative (empty)
import TypedRedex.Core.Redex
import TypedRedex.Core.Internal.Logic (Logic (Ground, Free), LogicType (..))
import TypedRedex.Interpreters.SubstRedex (runSubstRedex, takeS, Stream)
import TypedRedex.Interpreters.DeepRedex (DeepRedex, runDeep, formatAsRule, extractAllRules, deepVar)
import TypedRedex.Interpreters.TracingRedex (runWithDerivation, prettyDerivation, substInDerivation, Derivation(..))
import TypedRedex.Utils.Type (quote0, quote1, quote2, quote3)

-- PCF (Programming Computable Functions) with fixpoints
-- Small-step call-by-value operational semantics
--
-- Using inference-rule-style syntax for cleaner definitions.
-- Compare with the original pcf-step example to see the difference.

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

--------------------------------------------------------------------------------
-- Value predicate
--------------------------------------------------------------------------------

-- Values: lambdas, zero, and successors of values
--
--           value(v)
-- ───────   ────────────
-- value(λ)  value(succ v)
--
-- ─────────
-- value(0)

value :: (Redex rel) => L Tm rel -> Relation rel
value = relation "value" $ \t ->
  conde
    [ fresh $ \b -> t <=> lam b
    , t <=> zero
    , fresh $ \v -> do
        t <=> succTm v
        call (value v)
    ]

--------------------------------------------------------------------------------
-- Substitution (naive, non-capture-avoiding)
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Small-step operational semantics using inference-rule style
--------------------------------------------------------------------------------

-- Beta reduction:
--
--   value(v)   [v/x]body = e'
--   ─────────────────────────── [β]
--   (λx.body) v ⟶ e'

stepBeta :: (Redex rel) => L Tm rel -> L Tm rel -> Relation rel
stepBeta = rule2 "β" $ \concl ->
  fresh3 $ \body v e' -> do
    concl (app (lam body) v) e'
    call (value v)
    call (subst0 body v e')

-- Application left congruence:
--
--       e₁ ⟶ e₁'
--   ─────────────────── [app-L]
--   e₁ e₂ ⟶ e₁' e₂

stepAppL :: (Redex rel) => L Tm rel -> L Tm rel -> Relation rel
stepAppL = rule2 "app-L" $ \concl ->
  fresh3 $ \e1 e1' e2 -> do
    concl (app e1 e2) (app e1' e2)
    call (step e1 e1')

-- Application right congruence:
--
--   value(v)   e₂ ⟶ e₂'
--   ──────────────────────── [app-R]
--   v e₂ ⟶ v e₂'

stepAppR :: (Redex rel) => L Tm rel -> L Tm rel -> Relation rel
stepAppR = rule2 "app-R" $ \concl ->
  fresh3 $ \v e2 e2' -> do
    concl (app v e2) (app v e2')
    call (value v)
    call (step e2 e2')

-- Successor congruence:
--
--       e ⟶ e'
--   ─────────────────── [succ]
--   succ(e) ⟶ succ(e')

stepSucc :: (Redex rel) => L Tm rel -> L Tm rel -> Relation rel
stepSucc = rule2 "succ" $ \concl ->
  fresh2 $ \e e' -> do
    concl (succTm e) (succTm e')
    call (step e e')

-- Predecessor of zero (axiom):
--
--   ─────────────────── [pred-zero]
--   pred(0) ⟶ 0

stepPredZero :: (Redex rel) => L Tm rel -> L Tm rel -> Relation rel
stepPredZero = axiom2 "pred-zero" (predTm zero) zero

-- Predecessor of successor:
--
--   value(v)
--   ─────────────────────── [pred-succ]
--   pred(succ(v)) ⟶ v

stepPredSucc :: (Redex rel) => L Tm rel -> L Tm rel -> Relation rel
stepPredSucc = rule2 "pred-succ" $ \concl ->
  fresh $ \v -> do
    concl (predTm (succTm v)) v
    call (value v)

-- Predecessor congruence:
--
--       e ⟶ e'
--   ─────────────────── [pred]
--   pred(e) ⟶ pred(e')

stepPred :: (Redex rel) => L Tm rel -> L Tm rel -> Relation rel
stepPred = rule2 "pred" $ \concl ->
  fresh2 $ \e e' -> do
    concl (predTm e) (predTm e')
    call (step e e')

-- If-zero when condition is zero:
--
--   ───────────────────────────── [ifz-zero]
--   ifz(0, e₁, e₂) ⟶ e₁

stepIfzZero :: (Redex rel) => L Tm rel -> L Tm rel -> Relation rel
stepIfzZero = rule2 "ifz-zero" $ \concl ->
  fresh2 $ \e1 e2 ->
    concl (ifz zero e1 e2) e1

-- If-zero when condition is successor:
--
--   value(v)
--   ─────────────────────────────── [ifz-succ]
--   ifz(succ(v), e₁, e₂) ⟶ e₂

stepIfzSucc :: (Redex rel) => L Tm rel -> L Tm rel -> Relation rel
stepIfzSucc = rule2 "ifz-succ" $ \concl ->
  fresh3 $ \v e1 e2 -> do
    concl (ifz (succTm v) e1 e2) e2
    call (value v)

-- If-zero congruence:
--
--           e ⟶ e'
--   ─────────────────────────────── [ifz]
--   ifz(e, e₁, e₂) ⟶ ifz(e', e₁, e₂)

stepIfzCong :: (Redex rel) => L Tm rel -> L Tm rel -> Relation rel
stepIfzCong = rule2 "ifz" $ \concl ->
  fresh4 $ \e e' e1 e2 -> do
    concl (ifz e e1 e2) (ifz e' e1 e2)
    call (step e e')

-- Fixpoint unrolling:
--
--   ─────────────────────── [fix]
--   fix(e) ⟶ e (fix(e))

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

-- Run step with derivation tracing
type TracingStream a = Stream (a, Derivation)

stepWithTrace :: Tm -> TracingStream Tm
stepWithTrace t0 = runWithDerivation $ fresh $ \t' -> do
  _ <- embed $ step (Ground $ project t0) t'
  eval t'

-- Helper to extract all rules from a binary relation
printAllRules :: (L Tm DeepRedex -> L Tm DeepRedex -> Relation DeepRedex) -> IO ()
printAllRules rel = do
  let goal = runDeep $ do
        let Relation { relBody = body } = rel (deepVar 0) (deepVar 1)
        body
  let rules = extractAllRules goal
  mapM_ (\(name, ruleGoal) -> do
    putStrLn $ formatAsRule name ruleGoal
    putStrLn "") rules

main :: IO ()
main = do
  putStrLn "=== Automatic Rule Extraction (DeepRedex) ==="
  putStrLn ""

  -- Extract all step rules automatically
  printAllRules step

  putStrLn "=== PCF Small-Step Semantics (Execution) ==="
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

  putStrLn "=== Derivation Trees (TracingRedex) ==="
  putStrLn ""

  -- Example 1: pred(succ(0)) → 0
  -- Uses: step → pred-succ → value
  putStrLn "Example 1: pred(succ(0)) → 0"
  putStrLn "Expected: pred-succ rule with value premise"
  case takeS 1 (stepWithTrace ex1) of
    [(result, deriv)] -> do
      let deriv' = substInDerivation "x0" (showTm result) deriv
      putStrLn $ prettyDerivation deriv'
    _ -> putStrLn "No derivation found"

  -- Example 2: (λx.x) 0 → 0
  -- Uses: step → β → value, subst0 → subst0-var0
  putStrLn "Example 2: (λx.x) 0 → 0"
  putStrLn "Expected: β rule with value and subst0 premises"
  case takeS 1 (stepWithTrace ex3) of
    [(result, deriv)] -> do
      let deriv' = substInDerivation "x0" (showTm result) deriv
      putStrLn $ prettyDerivation deriv'
    _ -> putStrLn "No derivation found"

  -- Example 3: succ(pred(succ(0))) → succ(0)
  -- Uses: step → succ → step → pred-succ → value
  -- Shows congruence rule with nested step
  let ex4 = Succ (Pred (Succ Zero))
  putStrLn "Example 3: succ(pred(succ(0))) → succ(0)"
  putStrLn "Expected: succ congruence with nested pred-succ"
  case takeS 1 (stepWithTrace ex4) of
    [(result, deriv)] -> do
      let deriv' = substInDerivation "x0" (showTm result) deriv
      putStrLn $ prettyDerivation deriv'
    _ -> putStrLn "No derivation found"

  -- Example 4: ifz(pred(succ(0)), 1, 2) → ifz(0, 1, 2)
  -- Uses: step → ifz-cong → step → pred-succ → value
  -- Shows ifz congruence with nested step
  let ex5 = Ifz (Pred (Succ Zero)) (Succ Zero) (Succ (Succ Zero))
  putStrLn "Example 4: ifz(pred(succ(0)), 1, 2) → ifz(0, 1, 2)"
  putStrLn "Expected: ifz congruence with nested pred-succ"
  case takeS 1 (stepWithTrace ex5) of
    [(result, deriv)] -> do
      let deriv' = substInDerivation "x0" (showTm result) deriv
      putStrLn $ prettyDerivation deriv'
    _ -> putStrLn "No derivation found"

  -- Example 5: ifz(succ(0), 1, 2) → 2
  -- Uses: step → ifz-succ → value
  let ex6 = Ifz (Succ Zero) (Succ Zero) (Succ (Succ Zero))
  putStrLn "Example 5: ifz(succ(0), 1, 2) → 2"
  putStrLn "Expected: ifz-succ rule with value premise"
  case takeS 1 (stepWithTrace ex6) of
    [(result, deriv)] -> do
      let deriv' = substInDerivation "x0" (showTm result) deriv
      putStrLn $ prettyDerivation deriv'
    _ -> putStrLn "No derivation found"

  -- Example 6: ((λx.λy.x) 0) 1 → (λy.0) 1
  -- Uses: step → app-L → step → β → value, subst0
  -- Shows application left congruence with nested β
  let ex7 = App (App (Lam (Lam (Var (S Z)))) Zero) (Succ Zero)
  putStrLn "Example 6: ((λx.λy.x) 0) 1 → (λy.0) 1"
  putStrLn "Expected: app-L congruence with nested β reduction"
  case takeS 1 (stepWithTrace ex7) of
    [(result, deriv)] -> do
      let deriv' = substInDerivation "x0" (showTm result) deriv
      putStrLn $ prettyDerivation deriv'
    _ -> putStrLn "No derivation found"

  -- Example 7: (λx.succ(x)) 0 → succ(0)
  -- Uses: step → β → value, subst0 → subst0-succ → subst0-var0
  -- Shows substitution into succ
  let ex8 = App (Lam (Succ (Var Z))) Zero
  putStrLn "Example 7: (λx.succ(x)) 0 → succ(0)"
  putStrLn "Expected: β with substitution into succ"
  case takeS 1 (stepWithTrace ex8) of
    [(result, deriv)] -> do
      let deriv' = substInDerivation "x0" (showTm result) deriv
      putStrLn $ prettyDerivation deriv'
    _ -> putStrLn "No derivation found"

  -- Example 8: fix(λf.λx.x) → (λf.λx.x) fix(λf.λx.x)
  -- Uses: step → fix (axiom, no premises)
  let ex9 = Fix (Lam (Lam (Var Z)))
  putStrLn "Example 8: fix(λf.λx.x) → (λf.λx.x) fix(λf.λx.x)"
  putStrLn "Expected: fix unrolling (axiom)"
  case takeS 1 (stepWithTrace ex9) of
    [(result, deriv)] -> do
      let deriv' = substInDerivation "x0" (showTm result) deriv
      putStrLn $ prettyDerivation deriv'
    _ -> putStrLn "No derivation found"

  -- Example 9: (λx.x) (λy.y) → (λy.y)
  -- β reduction with lambda as argument
  let ex10 = App (Lam (Var Z)) (Lam (Var Z))
  putStrLn "Example 9: (λx.x) (λy.y) → (λy.y)"
  putStrLn "Expected: β with lambda value"
  case takeS 1 (stepWithTrace ex10) of
    [(result, deriv)] -> do
      let deriv' = substInDerivation "x0" (showTm result) deriv
      putStrLn $ prettyDerivation deriv'
    _ -> putStrLn "No derivation found"

  -- Example 10: pred(succ(succ(0))) → succ(0)
  -- pred-succ with nested succ value
  let ex11 = Pred (Succ (Succ Zero))
  putStrLn "Example 10: pred(succ(succ(0))) → succ(0)"
  putStrLn "Expected: pred-succ with nested value proof"
  case takeS 1 (stepWithTrace ex11) of
    [(result, deriv)] -> do
      let deriv' = substInDerivation "x0" (showTm result) deriv
      putStrLn $ prettyDerivation deriv'
    _ -> putStrLn "No derivation found"

  -- Example 11: ((λx.λy.y) 0) → (λy.y)
  -- β reduction, body doesn't use argument
  let ex12 = App (Lam (Lam (Var Z))) Zero
  putStrLn "Example 11: (λx.λy.y) 0 → (λy.y)"
  putStrLn "Expected: β with subst0-lam (lambda doesn't capture)"
  case takeS 1 (stepWithTrace ex12) of
    [(result, deriv)] -> do
      let deriv' = substInDerivation "x0" (showTm result) deriv
      putStrLn $ prettyDerivation deriv'
    _ -> putStrLn "No derivation found"

  -- Example 12: ifz(0, 0, succ(0)) → 0
  -- ifz-zero (simplest case)
  let ex13 = Ifz Zero Zero (Succ Zero)
  putStrLn "Example 12: ifz(0, 0, 1) → 0"
  putStrLn "Expected: ifz-zero (axiom-like, no premises)"
  case takeS 1 (stepWithTrace ex13) of
    [(result, deriv)] -> do
      let deriv' = substInDerivation "x0" (showTm result) deriv
      putStrLn $ prettyDerivation deriv'
    _ -> putStrLn "No derivation found"

  -- Example 13: (λf.f 0) (λx.succ(x)) → (λx.succ(x)) 0
  -- β reduction with function as argument, result is application
  let ex14 = App (Lam (App (Var Z) Zero)) (Lam (Succ (Var Z)))
  putStrLn "Example 13: (λf.f 0) (λx.succ(x)) → (λx.succ(x)) 0"
  putStrLn "Expected: β with complex subst0-app"
  case takeS 1 (stepWithTrace ex14) of
    [(result, deriv)] -> do
      let deriv' = substInDerivation "x0" (showTm result) deriv
      putStrLn $ prettyDerivation deriv'
    _ -> putStrLn "No derivation found"

  -- Example 14: pred(0) → 0
  -- pred-zero axiom
  let ex15 = Pred Zero
  putStrLn "Example 14: pred(0) → 0"
  putStrLn "Expected: pred-zero (axiom)"
  case takeS 1 (stepWithTrace ex15) of
    [(result, deriv)] -> do
      let deriv' = substInDerivation "x0" (showTm result) deriv
      putStrLn $ prettyDerivation deriv'
    _ -> putStrLn "No derivation found"

  -- Example 15: (λx.pred(x)) succ(0) → pred(succ(0))
  -- β with subst into pred
  let ex16 = App (Lam (Pred (Var Z))) (Succ Zero)
  putStrLn "Example 15: (λx.pred(x)) succ(0) → pred(succ(0))"
  putStrLn "Expected: β with subst0-pred"
  case takeS 1 (stepWithTrace ex16) of
    [(result, deriv)] -> do
      let deriv' = substInDerivation "x0" (showTm result) deriv
      putStrLn $ prettyDerivation deriv'
    _ -> putStrLn "No derivation found"

  -- Example 16: (succ(0)) applied to nothing - value, no step
  -- This should have NO derivation (values don't step)
  let ex17 = Succ Zero
  putStrLn "Example 16: succ(0) (value - should not step)"
  putStrLn "Expected: No derivation (values are stuck)"
  case takeS 1 (stepWithTrace ex17) of
    [] -> putStrLn "Correct: No derivation found (value doesn't step)\n"
    [(result, deriv)] -> do
      putStrLn "Unexpected: found a step"
      let deriv' = substInDerivation "x0" (showTm result) deriv
      putStrLn $ prettyDerivation deriv'

-- Helper to show a term nicely
showTm :: Tm -> String
showTm Zero = "0"
showTm (Succ e) = "succ(" ++ showTm e ++ ")"
showTm (Pred e) = "pred(" ++ showTm e ++ ")"
showTm (Var Z) = "x"
showTm (Var (S n)) = "y" ++ show (natToInt n)
showTm (Lam b) = "(λ." ++ showTm b ++ ")"
showTm (App f a) = "(" ++ showTm f ++ " " ++ showTm a ++ ")"
showTm (Ifz c t e) = "ifz(" ++ showTm c ++ ", " ++ showTm t ++ ", " ++ showTm e ++ ")"
showTm (Fix e) = "fix(" ++ showTm e ++ ")"

natToInt :: Nat -> Int
natToInt Z = 0
natToInt (S n) = 1 + natToInt n
