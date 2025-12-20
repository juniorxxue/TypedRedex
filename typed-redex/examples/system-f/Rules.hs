{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RebindableSyntax #-}

-- | Mode-checked System F typing rules.
--
-- This module uses RebindableSyntax so rule bodies can use plain 'do'.
module Rules
  ( -- * Judgments
    lookupTm, typeof
    -- * Wrong-order version (for testing runtime scheduling)
  , assertEq, typeofWrongOrder
  ) where

import Prelude hiding ((>>=), (>>), return)
import TypedRedex hiding (fresh, fresh2, fresh3, fresh4, fresh5, fresh6, ground, lift1, lift2, lift3, neg)
import TypedRedex.Core.Internal.Logic (Logic (Ground), LogicType (..))
import TypedRedex.Nominal (instantiateTo)
import TypedRedex.Nominal.Prelude
import TypedRedex.Interp.Subst (RedexFresh(..))
import TypedRedex.DSL.Fresh (LTerm)
import TypedRedex.DSL.Moded
  ( Mode(..), T(..)
  , AppliedM(..), defJudge3, ModedRule(..)
  , fresh, fresh2, fresh3, fresh4, fresh5, fresh6, prem, concl, liftRelDeferred
  , ground, Union
  , return, (>>=), (>>)
  )

import Syntax

--------------------------------------------------------------------------------
-- Mode-checked lookup: lookupTm ctx x ty
-- Modes: I, I, O
--------------------------------------------------------------------------------

lookupTm :: (RedexFresh rel, RedexEval rel, RedexNeg rel)
         => T vs1 Ctx rel -> T vs2 Nom rel -> T vs3 Ty rel
         -> AppliedM rel "lookupTm" '[I, I, O] '[vs1, vs2, vs3] '[Ctx, Nom, Ty]
lookupTm = defJudge3 @"lookupTm" $ \rule ->
  [ -- lookup-here: lookupTm (x:ty, rest) x ty
    rule "lookup-here" $ do
      (ty, rest, x) <- fresh3
      concl $ lookupTm (tmBind x ty rest) x ty

  , -- lookup-there: lookupTm (y:tyY, rest) x ty ← lookupTm rest x ty
    rule "lookup-there" $ do
      (x, y, ty, tyY, rest) <- fresh5
      concl $ lookupTm (tmBind y tyY rest) x ty
      prem $ lookupTm rest x ty

  , -- lookup-skip: lookupTm (alpha, rest) x ty ← lookupTm rest x ty
    rule "lookup-skip" $ do
      (alpha, x, ty, rest) <- fresh4
      concl $ lookupTm (tyBind alpha rest) x ty
      prem $ lookupTm rest x ty
  ]

--------------------------------------------------------------------------------
-- Mode-checked typeof: typeof ctx e ty
-- Modes: I, I, O
--------------------------------------------------------------------------------

typeof :: (RedexFresh rel, RedexEval rel, RedexNeg rel)
       => T vs1 Ctx rel -> T vs2 Tm rel -> T vs3 Ty rel
       -> AppliedM rel "typeof" '[I, I, O] '[vs1, vs2, vs3] '[Ctx, Tm, Ty]
typeof = defJudge3 @"typeof" $ \rule ->
  [ -- typeof-unit: typeof ctx () Unit
    rule "typeof-unit" $ do
      ctx <- fresh
      concl $ typeof ctx unit tunit

  , -- typeof-var: typeof ctx (Var x) ty ← lookupTm ctx x ty
    rule "typeof-var" $ do
      (ctx, x, ty) <- fresh3
      concl $ typeof ctx (var x) ty
      prem $ lookupTm ctx x ty

  , -- typeof-lam: typeof ctx (Lam tyA (bind x body)) (tyA -> tyB)
    --             ← typeof (x:tyA, ctx) body tyB
    rule "typeof-lam" $ do
      (ctx, tyA, x, body, tyB) <- fresh5
      concl $ typeof ctx (lam tyA (bindNomPat x body)) (tarr tyA tyB)
      prem $ typeof (tmBind x tyA ctx) body tyB

  , -- typeof-app: typeof ctx (App e1 e2) tyB
    --             ← typeof ctx e1 (tyA -> tyB) ∧ typeof ctx e2 tyA
    rule "typeof-app" $ do
      (ctx, e1, e2, tyA, tyB) <- fresh5
      concl $ typeof ctx (app e1 e2) tyB
      prem $ typeof ctx e1 (tarr tyA tyB)
      prem $ typeof ctx e2 tyA

  , -- typeof-tlam: typeof ctx (TLam (bind alpha body)) (forall alpha. tyBody)
    --              ← typeof (alpha, ctx) body tyBody
    rule "typeof-tlam" $ do
      (ctx, alpha, body, tyBody) <- fresh4
      prem $ typeof (tyBind alpha ctx) body tyBody
      concl $ typeof ctx (tlam (bindTyPat alpha body)) (tall (bindTyPat alpha tyBody))

  , -- typeof-tapp: typeof ctx (TApp e tyArg) result
    --              ← typeof ctx e (forall. tyBnd) ∧ instantiateTo tyBnd tyArg result
    rule "typeof-tapp" $ do
      (ctx, e, tyArg, tyBnd, result) <- fresh5
      concl $ typeof ctx (tapp e tyArg) result
      prem $ typeof ctx e (tall tyBnd)
      liftRelDeferred $ instantiateTo (tTerm tyBnd) (tTerm tyArg) (tTerm result)
  ]

--------------------------------------------------------------------------------
-- WRONG ORDER typeof: Demonstrates runtime scheduling
--------------------------------------------------------------------------------

-- | A helper judgment for demonstrating forced reordering.
-- Mode [I, I, I]: ALL arguments must be ground (inputs).
assertEq :: (RedexFresh rel, RedexEval rel, RedexNeg rel)
         => T vs1 Ty rel -> T vs2 Ty rel -> T vs3 Tm rel
         -> AppliedM rel "assertEq" '[I, I, I] '[vs1, vs2, vs3] '[Ty, Ty, Tm]
assertEq = defJudge3 @"assertEq" $ \rule ->
  [ rule "eq" $ do
      ty <- fresh
      concl $ assertEq ty ty unit
  ]

-- | typeof with DELIBERATELY WRONG premise order.
typeofWrongOrder :: (RedexFresh rel, RedexEval rel, RedexNeg rel)
                 => T vs1 Ctx rel -> T vs2 Tm rel -> T vs3 Ty rel
                 -> AppliedM rel "typeof-wrong" '[I, I, O] '[vs1, vs2, vs3] '[Ctx, Tm, Ty]
typeofWrongOrder = defJudge3 @"typeof-wrong" $ \rule ->
  [ -- typeof-unit: normal order (baseline)
    rule "typeof-unit" $ do
      ctx <- fresh
      concl $ typeofWrongOrder ctx unit tunit

  , -- typeof-var: prem BEFORE concl (wrong order)
    rule "typeof-var" $ do
      (ctx, x, ty) <- fresh3
      prem $ lookupTm ctx x ty  -- prem first!
      concl $ typeofWrongOrder ctx (var x) ty

  , -- typeof-lam: prem BEFORE concl (wrong order)
    rule "typeof-lam" $ do
      (ctx, tyA, x, body, tyB) <- fresh5
      prem $ typeofWrongOrder (tmBind x tyA ctx) body tyB  -- prem first!
      concl $ typeofWrongOrder ctx (lam tyA (bindNomPat x body)) (tarr tyA tyB)

  , -- typeof-app: FORCED REORDERING TEST
    rule "typeof-app" $ do
      (ctx, e1, e2, tyA, tyB, tyA2) <- fresh6
      -- WRONG ORDER - would fail without scheduling:
      prem $ assertEq tyA tyA2 unit                        -- needs {3,5} - NOT READY initially
      prem $ typeofWrongOrder ctx e2 tyA2                  -- needs {0,2}, produces {5}
      prem $ typeofWrongOrder ctx e1 (tarr tyA tyB)        -- needs {0,1}, produces {3,4}
      concl $ typeofWrongOrder ctx (app e1 e2) tyB

  , -- typeof-tlam: prem BEFORE concl (wrong order)
    rule "typeof-tlam" $ do
      (ctx, alpha, body, tyBody) <- fresh4
      prem $ typeofWrongOrder (tyBind alpha ctx) body tyBody  -- prem first!
      concl $ typeofWrongOrder ctx (tlam (bindTyPat alpha body)) (tall (bindTyPat alpha tyBody))

  , -- typeof-tapp: prem BEFORE concl (wrong order)
    rule "typeof-tapp" $ do
      (ctx, e, tyArg, tyBnd, result) <- fresh5
      prem $ typeofWrongOrder ctx e (tall tyBnd)  -- prem first!
      concl $ typeofWrongOrder ctx (tapp e tyArg) result
      liftRelDeferred $ instantiateTo (tTerm tyBnd) (tTerm tyArg) (tTerm result)
  ]
