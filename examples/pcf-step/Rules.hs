{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RebindableSyntax #-}

-- | Mode-checked PCF small-step semantics rules.
--
-- This module uses RebindableSyntax so rule bodies can use plain 'do'.
module Rules
  ( -- * Syntax re-exports
    Nat(..), Tm(..)
  , zro, suc
  , var, lam, app, zero, succTm, predTm, ifz, fix
    -- * Judgments
  , value, subst0, step
  ) where

import Prelude hiding ((>>=), (>>), return)
import Control.Applicative (empty)
import Data.Proxy (Proxy(..))
import TypedRedex hiding (fresh, fresh2, fresh3, fresh4, fresh5, ground, lift1, lift2, lift3, neg)
import TypedRedex.Logic (Field(..))
import TypedRedex.Interp.PrettyPrint (TypesetNaming(..))
import TypedRedex.DSL.Type (quote0, quote1, quote2, quote3)
import TypedRedex.DSL.Fresh (LTerm)
import TypedRedex.DSL.Moded
  ( Mode(..), T(..)
  , AppliedM(..), Judgment1, Judgment2, Judgment3, defJudge1, defJudge2, defJudge3, ModedRule(..)
  , fresh, fresh2, fresh3, fresh4, fresh5, prem, concl
  , ground, lift1, lift2, lift3, Union
  , return, (>>=), (>>)
  )

--------------------------------------------------------------------------------
-- Natural numbers for de Bruijn indices
--------------------------------------------------------------------------------

data Nat = Z | S Nat deriving (Eq, Show)

instance TypesetNaming Nat  -- uses default

instance LogicType Nat where
  data Reified Nat var = ZR | SR (Logic Nat var)

  project Z = ZR
  project (S n) = SR (Ground $ project n)

  reify ZR = Just Z
  reify (SR (Ground n)) = S <$> reify n
  reify _ = Nothing

  quote ZR = quote0 "Z"
  quote (SR n) = quote1 "S" n

  children ZR = []
  children (SR n) = [Field (Proxy :: Proxy Nat) n]

  unifyVal _ ZR ZR = pure ()
  unifyVal unif (SR x) (SR y) = unif x y
  unifyVal _ _ _ = empty

  derefVal _ ZR = pure Z
  derefVal deref (SR n) = S <$> deref n

-- Raw constructors
zro_ :: Logic Nat var
zro_ = Ground ZR

suc_ :: Logic Nat var -> Logic Nat var
suc_ = Ground . SR

-- Moded constructors
zro :: T '[] Nat rel
zro = ground zro_

suc :: T vs Nat rel -> T vs Nat rel
suc = lift1 suc_

--------------------------------------------------------------------------------
-- PCF Terms
--------------------------------------------------------------------------------

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

instance TypesetNaming Tm  -- uses default

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

  quote (VarR n) = quote1 "Var" n
  quote (LamR b) = quote1 "Lam" b
  quote (AppR f a) = quote2 "App" f a
  quote ZeroR = quote0 "Zero"
  quote (SuccR e) = quote1 "Succ" e
  quote (PredR e) = quote1 "Pred" e
  quote (IfzR e e1 e2) = quote3 "Ifz" e e1 e2
  quote (FixR e) = quote1 "Fix" e

  children (VarR n) = [Field (Proxy :: Proxy Nat) n]
  children (LamR b) = [Field (Proxy :: Proxy Tm) b]
  children (AppR f a) = [Field (Proxy :: Proxy Tm) f, Field (Proxy :: Proxy Tm) a]
  children ZeroR = []
  children (SuccR e) = [Field (Proxy :: Proxy Tm) e]
  children (PredR e) = [Field (Proxy :: Proxy Tm) e]
  children (IfzR e e1 e2) = [Field (Proxy :: Proxy Tm) e, Field (Proxy :: Proxy Tm) e1, Field (Proxy :: Proxy Tm) e2]
  children (FixR e) = [Field (Proxy :: Proxy Tm) e]

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

-- Raw constructors
var_ :: Logic Nat var -> Logic Tm var
var_ = Ground . VarR

lam_ :: Logic Tm var -> Logic Tm var
lam_ = Ground . LamR

app_ :: Logic Tm var -> Logic Tm var -> Logic Tm var
app_ f a = Ground $ AppR f a

zero_ :: Logic Tm var
zero_ = Ground ZeroR

succTm_ :: Logic Tm var -> Logic Tm var
succTm_ = Ground . SuccR

predTm_ :: Logic Tm var -> Logic Tm var
predTm_ = Ground . PredR

ifz_ :: Logic Tm var -> Logic Tm var -> Logic Tm var -> Logic Tm var
ifz_ e e1 e2 = Ground $ IfzR e e1 e2

fix_ :: Logic Tm var -> Logic Tm var
fix_ = Ground . FixR

-- Moded constructors
var :: T vs Nat rel -> T vs Tm rel
var = lift1 var_

lam :: T vs Tm rel -> T vs Tm rel
lam = lift1 lam_

app :: T vs1 Tm rel -> T vs2 Tm rel -> T (Union vs1 vs2) Tm rel
app = lift2 app_

zero :: T '[] Tm rel
zero = ground zero_

succTm :: T vs Tm rel -> T vs Tm rel
succTm = lift1 succTm_

predTm :: T vs Tm rel -> T vs Tm rel
predTm = lift1 predTm_

ifz :: T vs1 Tm rel -> T vs2 Tm rel -> T vs3 Tm rel -> T (Union vs1 (Union vs2 vs3)) Tm rel
ifz = lift3 ifz_

fix :: T vs Tm rel -> T vs Tm rel
fix = lift1 fix_

--------------------------------------------------------------------------------
-- Value predicate (moded)
-- Mode: [I]
--------------------------------------------------------------------------------

value :: RedexNeg rel => Judgment1 rel "value" '[I] Tm
value = defJudge1 @"value" $ \rule ->
  [ rule "value-lam" $ do
      b <- fresh
      concl $ value (lam b)

  , rule "value-zero" $ do
      concl $ value zero

  , rule "value-succ" $ do
      v <- fresh
      concl $ value (succTm v)
      prem $ value v
  ]

--------------------------------------------------------------------------------
-- Substitution (moded)
-- Mode: [I, I, O]
-- subst0 body arg out means [arg/0]body = out
--------------------------------------------------------------------------------

subst0 :: RedexNeg rel => Judgment3 rel "subst0" '[I, I, O] Tm Tm Tm
subst0 = defJudge3 @"subst0" $ \rule ->
  [ -- Lambda: don't substitute under binder (naive, non-capture-avoiding)
    rule "subst0-lam" $ do
      (b, arg) <- fresh2
      concl $ subst0 (lam b) arg (lam b)

  , -- Variable at index 0: replace with arg
    rule "subst0-var0" $ do
      arg <- fresh
      concl $ subst0 (var zro) arg arg

  , -- Variable at index n+1: decrement to n
    rule "subst0-varS" $ do
      (n', arg) <- fresh2
      concl $ subst0 (var (suc n')) arg (var n')

  , -- Application
    rule "subst0-app" $ do
      (f, a, arg, f', a') <- fresh5
      concl $ subst0 (app f a) arg (app f' a')
      prem $ subst0 f arg f'
      prem $ subst0 a arg a'

  , -- Zero
    rule "subst0-zero" $ do
      arg <- fresh
      concl $ subst0 zero arg zero

  , -- Succ
    rule "subst0-succ" $ do
      (e, arg, e') <- fresh3
      concl $ subst0 (succTm e) arg (succTm e')
      prem $ subst0 e arg e'

  , -- Pred
    rule "subst0-pred" $ do
      (e, arg, e') <- fresh3
      concl $ subst0 (predTm e) arg (predTm e')
      prem $ subst0 e arg e'

  , -- Ifz
    rule "subst0-ifz" $ do
      (e, e1, e2, arg) <- fresh4
      (e', e1', e2') <- fresh3
      concl $ subst0 (ifz e e1 e2) arg (ifz e' e1' e2')
      prem $ subst0 e arg e'
      prem $ subst0 e1 arg e1'
      prem $ subst0 e2 arg e2'

  , -- Fix
    rule "subst0-fix" $ do
      (e, arg, e') <- fresh3
      concl $ subst0 (fix e) arg (fix e')
      prem $ subst0 e arg e'
  ]

--------------------------------------------------------------------------------
-- Small-step operational semantics (moded)
-- Mode: [I, O]
--------------------------------------------------------------------------------

step :: RedexNeg rel => Judgment2 rel "step" '[I, O] Tm Tm
step = defJudge2 @"step" $ \rule ->
  [ -- Beta reduction
    rule "β" $ do
      (body, v, e') <- fresh3
      concl $ step (app (lam body) v) e'
      prem $ value v
      prem $ subst0 body v e'

  , -- Application left congruence
    rule "app-L" $ do
      (e1, e1', e2) <- fresh3
      concl $ step (app e1 e2) (app e1' e2)
      prem $ step e1 e1'

  , -- Application right congruence
    rule "app-R" $ do
      (v, e2, e2') <- fresh3
      concl $ step (app v e2) (app v e2')
      prem $ value v
      prem $ step e2 e2'

  , -- Successor congruence
    rule "succ" $ do
      (e, e') <- fresh2
      concl $ step (succTm e) (succTm e')
      prem $ step e e'

  , -- Predecessor of zero (axiom)
    rule "pred-zero" $ do
      concl $ step (predTm zero) zero

  , -- Predecessor of successor
    rule "pred-succ" $ do
      v <- fresh
      concl $ step (predTm (succTm v)) v
      prem $ value v

  , -- Predecessor congruence
    rule "pred" $ do
      (e, e') <- fresh2
      concl $ step (predTm e) (predTm e')
      prem $ step e e'

  , -- If-zero when condition is zero
    rule "ifz-zero" $ do
      (e1, e2) <- fresh2
      concl $ step (ifz zero e1 e2) e1

  , -- If-zero when condition is successor
    rule "ifz-succ" $ do
      (v, e1, e2) <- fresh3
      concl $ step (ifz (succTm v) e1 e2) e2
      prem $ value v

  , -- If-zero congruence
    rule "ifz" $ do
      (e, e', e1, e2) <- fresh4
      concl $ step (ifz e e1 e2) (ifz e' e1 e2)
      prem $ step e e'

  , -- Fixpoint unrolling
    rule "fix" $ do
      e <- fresh
      concl $ step (fix e) (app e (fix e))
  ]
