{-# LANGUAGE DataKinds, TypeApplications #-}
{-# LANGUAGE RebindableSyntax #-}

-- | STLC Bidirectional Rules - Clean syntax demo
--
-- Uses RebindableSyntax for plain @do@ notation.
-- No explicit type applications needed - inference works!
module HKT.Example.Rules
  ( -- * Judgments
    check, synth, lookupCtx
    -- * Rules
  , checkRules, synthRules, lookupRules
  ) where

import Prelude hiding ((>>=), (>>), return)
import HKT.Core
import HKT.Moded
import HKT.Example.Syntax

--------------------------------------------------------------------------------
-- Judgments
--------------------------------------------------------------------------------

-- | Γ ⊢ e ⇐ A (checking mode: all inputs)
check :: MJudgment3 "check" 'I CtxF 'I ExprF 'I TyF
check = mjudge3 checkRules

-- | Γ ⊢ e ⇒ A (synthesis mode: type is output)
synth :: MJudgment3 "synth" 'I CtxF 'I ExprF 'O TyF
synth = mjudge3 synthRules

-- | Γ(n) = A (lookup)
lookupCtx :: MJudgment3 "lookup" 'I CtxF 'I ExprF 'O TyF
lookupCtx = mjudge3 lookupRules

--------------------------------------------------------------------------------
-- Check Rules
--------------------------------------------------------------------------------

checkRules :: [ModedRule]
checkRules =
  [ -- Γ, A ⊢ e ⇐ B
    -- ─────────────────── [⇐λ]
    -- Γ ⊢ λe ⇐ A → B
    ruleM @"⇐λ" $ do
      (ctx, body, a, b) <- fresh4
      concl $ check ctx (elam body) (tarr a b)
      prem  $ check (ccons a ctx) body b

    -- Γ ⊢ e ⇒ A
    -- ───────────── [⇐Sub]
    -- Γ ⊢ e ⇐ A
  , ruleM @"⇐Sub" $ do
      (ctx, e, ty) <- fresh3
      concl $ check ctx e ty
      prem  $ synth ctx e ty
  ]

--------------------------------------------------------------------------------
-- Synth Rules
--------------------------------------------------------------------------------

synthRules :: [ModedRule]
synthRules =
  [ -- ─────────────────── [⇒Unit]
    -- Γ ⊢ () ⇒ Unit
    ruleM @"⇒Unit" $ do
      ctx <- fresh
      concl $ synth ctx eunit tunit

    -- Γ(x) = A
    -- ───────────── [⇒Var]
    -- Γ ⊢ x ⇒ A
  , ruleM @"⇒Var" $ do
      (ctx, x, ty) <- fresh3
      concl $ synth ctx x ty
      prem  $ lookupCtx ctx x ty

    -- Γ ⊢ e₁ ⇒ A → B    Γ ⊢ e₂ ⇐ A
    -- ─────────────────────────────── [⇒App]
    -- Γ ⊢ e₁ e₂ ⇒ B
  , ruleM @"⇒App" $ do
      (ctx, e1, e2, a, b) <- fresh5
      concl $ synth ctx (eapp e1 e2) b
      prem  $ synth ctx e1 (tarr a b)
      prem  $ check ctx e2 a

    -- Γ ⊢ e ⇐ A
    -- ─────────────── [⇒Ann]
    -- Γ ⊢ (e : A) ⇒ A
  , ruleM @"⇒Ann" $ do
      (ctx, e, ty) <- fresh3
      concl $ synth ctx (eann e ty) ty
      prem  $ check ctx e ty
  ]

--------------------------------------------------------------------------------
-- Lookup Rules
--------------------------------------------------------------------------------

lookupRules :: [ModedRule]
lookupRules =
  [ -- ───────────────────── [Here]
    -- (Γ, A)(0) = A
    ruleM @"Here" $ do
      (ctx, ty) <- fresh2
      concl $ lookupCtx (ccons ty ctx) (evar 0) ty

    -- Γ(n) = A
    -- ─────────────────── [There]
    -- (Γ, B)(n+1) = A
  , ruleM @"There" $ do
      (ctx, n, ty, ty') <- fresh4
      concl $ lookupCtx (ccons ty' ctx) (succ_ n) ty
      prem  $ lookupCtx ctx n ty
  ]
  where
    -- Successor for de Bruijn indices
    succ_ :: T vs ExprF -> T vs ExprF
    succ_ (T v (Con (EVar i))) = T v (Con (EVar (i + 1)))
    succ_ t = t
