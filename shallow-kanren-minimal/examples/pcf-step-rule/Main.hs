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

value :: (Kanren rel) => L Tm rel -> Relation rel
value = relation "value" $ \t ->
  conde
    [ fresh $ \b -> t <=> lam b
    , t <=> zero
    , fresh $ \v ->
        t <=> succTm v *>
        call (value v)
    ]

--------------------------------------------------------------------------------
-- Substitution (naive, non-capture-avoiding)
--------------------------------------------------------------------------------

-- subst0 body arg out means [arg/0]body = out

-- Lambda: don't substitute under binder
subst0Lam :: (Kanren rel) => L Tm rel -> L Tm rel -> L Tm rel -> Relation rel
subst0Lam = rule3 "subst0-lam" $ \concl ->
  fresh2 $ \b arg ->
    concl (lam b) arg (lam b)

-- Variable at index 0: replace with arg
subst0Var0 :: (Kanren rel) => L Tm rel -> L Tm rel -> L Tm rel -> Relation rel
subst0Var0 = rule3 "subst0-var0" $ \concl ->
  fresh $ \arg ->
    concl (var zro) arg arg

-- Variable at index n+1: decrement to n
subst0VarS :: (Kanren rel) => L Tm rel -> L Tm rel -> L Tm rel -> Relation rel
subst0VarS = rule3 "subst0-varS" $ \concl ->
  fresh2 $ \n' arg ->
    concl (var (suc n')) arg (var n')

-- Application
subst0App :: (Kanren rel) => L Tm rel -> L Tm rel -> L Tm rel -> Relation rel
subst0App = rule3 "subst0-app" $ \concl ->
  fresh5 $ \f a arg f' a' ->
    concl (app f a) arg (app f' a') *>
    call (subst0 f arg f') *>
    call (subst0 a arg a')

-- Zero
subst0Zero :: (Kanren rel) => L Tm rel -> L Tm rel -> L Tm rel -> Relation rel
subst0Zero = rule3 "subst0-zero" $ \concl ->
  fresh $ \arg ->
    concl zero arg zero

-- Succ
subst0Succ :: (Kanren rel) => L Tm rel -> L Tm rel -> L Tm rel -> Relation rel
subst0Succ = rule3 "subst0-succ" $ \concl ->
  fresh3 $ \e arg e' ->
    concl (succTm e) arg (succTm e') *>
    call (subst0 e arg e')

-- Pred
subst0Pred :: (Kanren rel) => L Tm rel -> L Tm rel -> L Tm rel -> Relation rel
subst0Pred = rule3 "subst0-pred" $ \concl ->
  fresh3 $ \e arg e' ->
    concl (predTm e) arg (predTm e') *>
    call (subst0 e arg e')

-- Ifz
subst0Ifz :: (Kanren rel) => L Tm rel -> L Tm rel -> L Tm rel -> Relation rel
subst0Ifz = rule3 "subst0-ifz" $ \concl ->
  fresh4 $ \e e1 e2 arg -> fresh3 $ \e' e1' e2' ->
    concl (ifz e e1 e2) arg (ifz e' e1' e2') *>
    call (subst0 e arg e') *>
    call (subst0 e1 arg e1') *>
    call (subst0 e2 arg e2')

-- Fix
subst0Fix :: (Kanren rel) => L Tm rel -> L Tm rel -> L Tm rel -> Relation rel
subst0Fix = rule3 "subst0-fix" $ \concl ->
  fresh3 $ \e arg e' ->
    concl (fix e) arg (fix e') *>
    call (subst0 e arg e')

-- Combined substitution relation
subst0 :: (Kanren rel) => L Tm rel -> L Tm rel -> L Tm rel -> Relation rel
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

stepBeta :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
stepBeta = rule2 "β" $ \concl ->
  fresh3 $ \body v e' ->
    concl (app (lam body) v) e' *>
    call (value v) *>
    call (subst0 body v e')

-- Application left congruence:
--
--       e₁ ⟶ e₁'
--   ─────────────────── [app-L]
--   e₁ e₂ ⟶ e₁' e₂

stepAppL :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
stepAppL = rule2 "app-L" $ \concl ->
  fresh3 $ \e1 e1' e2 ->
    concl (app e1 e2) (app e1' e2) *>
    call (step e1 e1')

-- Application right congruence:
--
--   value(v)   e₂ ⟶ e₂'
--   ──────────────────────── [app-R]
--   v e₂ ⟶ v e₂'

stepAppR :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
stepAppR = rule2 "app-R" $ \concl ->
  fresh3 $ \v e2 e2' ->
    concl (app v e2) (app v e2') *>
    call (value v) *>
    call (step e2 e2')

-- Successor congruence:
--
--       e ⟶ e'
--   ─────────────────── [succ]
--   succ(e) ⟶ succ(e')

stepSucc :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
stepSucc = rule2 "succ" $ \concl ->
  fresh2 $ \e e' ->
    concl (succTm e) (succTm e') *>
    call (step e e')

-- Predecessor of zero (axiom):
--
--   ─────────────────── [pred-zero]
--   pred(0) ⟶ 0

stepPredZero :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
stepPredZero = axiom2 "pred-zero" (predTm zero) zero

-- Predecessor of successor:
--
--   value(v)
--   ─────────────────────── [pred-succ]
--   pred(succ(v)) ⟶ v

stepPredSucc :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
stepPredSucc = rule2 "pred-succ" $ \concl ->
  fresh $ \v ->
    concl (predTm (succTm v)) v *>
    call (value v)

-- Predecessor congruence:
--
--       e ⟶ e'
--   ─────────────────── [pred]
--   pred(e) ⟶ pred(e')

stepPred :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
stepPred = rule2 "pred" $ \concl ->
  fresh2 $ \e e' ->
    concl (predTm e) (predTm e') *>
    call (step e e')

-- If-zero when condition is zero:
--
--   ───────────────────────────── [ifz-zero]
--   ifz(0, e₁, e₂) ⟶ e₁

stepIfzZero :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
stepIfzZero = rule2 "ifz-zero" $ \concl ->
  fresh2 $ \e1 e2 ->
    concl (ifz zero e1 e2) e1

-- If-zero when condition is successor:
--
--   value(v)
--   ─────────────────────────────── [ifz-succ]
--   ifz(succ(v), e₁, e₂) ⟶ e₂

stepIfzSucc :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
stepIfzSucc = rule2 "ifz-succ" $ \concl ->
  fresh3 $ \v e1 e2 ->
    concl (ifz (succTm v) e1 e2) e2 *>
    call (value v)

-- If-zero congruence:
--
--           e ⟶ e'
--   ─────────────────────────────── [ifz]
--   ifz(e, e₁, e₂) ⟶ ifz(e', e₁, e₂)

stepIfzCong :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
stepIfzCong = rule2 "ifz" $ \concl ->
  fresh4 $ \e e' e1 e2 ->
    concl (ifz e e1 e2) (ifz e' e1 e2) *>
    call (step e e')

-- Fixpoint unrolling:
--
--   ─────────────────────── [fix]
--   fix(e) ⟶ e (fix(e))

stepFix :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
stepFix = rule2 "fix" $ \concl ->
  fresh $ \e ->
    concl (fix e) (app e (fix e))

-- Combined step relation
step :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
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
stepIO t0 = runSubstKanren $ fresh $ \t' -> do
  _ <- embed $ step (Ground $ project t0) t'
  eval t'

main :: IO ()
main = do
  putStrLn "=== PCF Small-Step Semantics (Inference-Rule Style) ==="
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
  putStrLn ""

  putStrLn "=== Syntax Comparison ==="
  putStrLn ""
  putStrLn "OLD STYLE (explicit <=>):"
  putStrLn "  stepAppL = relation2 \"step_appL\" $ \\t t' -> fresh3 $ \\e1 e1' e2 ->"
  putStrLn "    t <=> app e1 e2 *>"
  putStrLn "    call (step e1 e1') *>"
  putStrLn "    t' <=> app e1' e2"
  putStrLn ""
  putStrLn "NEW STYLE (inference rule with concl):"
  putStrLn "  stepAppL = rule2 \"app-L\" $ \\concl ->"
  putStrLn "    fresh3 $ \\e1 e1' e2 ->"
  putStrLn "      concl (app e1 e2) (app e1' e2) *>"
  putStrLn "      call (step e1 e1')"
  putStrLn ""
  putStrLn "The new style matches the inference rule:"
  putStrLn "      e₁ ⟶ e₁'"
  putStrLn "  ─────────────────── [app-L]"
  putStrLn "  e₁ e₂ ⟶ e₁' e₂"
