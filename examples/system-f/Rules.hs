{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RebindableSyntax #-}

-- | Mode-checked System F typing rules.
--
-- This module uses RebindableSyntax so rule bodies can use plain 'do'.
module Rules
  ( -- * Judgments
    lookupTm, typeof, substTy
  ) where

import Prelude hiding ((>>=), (>>), return)
import TypedRedex hiding (fresh, fresh2, fresh3, fresh4, fresh5, fresh6, ground, lift1, lift2, lift3, neg)
import TypedRedex.Logic (RedexHash)
import TypedRedex.Nominal (Substo(..), RedexFresh(..))
import TypedRedex.Nominal.Prelude
import TypedRedex.DSL.Fresh (LTerm)
import TypedRedex.DSL.Moded
  ( Mode(..), T(..)
  , AppliedM(..), Judgment3, Judgment4, defJudge3, defJudge4, ModedRule(..)
  , fresh, fresh2, fresh3, fresh4, fresh5, fresh6, prem, concl, liftRelDeferred
  , ground, Union
  , return, (>>=), (>>)
  )

import Syntax

--------------------------------------------------------------------------------
-- Mode-checked lookup: lookupTm ctx x ty
-- Modes: I, I, O
--------------------------------------------------------------------------------

type SystemFRel rel = (RedexFresh rel, RedexEval rel, RedexNeg rel, RedexHash rel)

lookupTm :: SystemFRel rel => Judgment3 rel "lookupTm" '[I, I, O] Ctx Nom Ty
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
-- Type substitution: substTy alpha tyArg tyBody result
-- Represents: [tyArg/alpha]tyBody = result
-- Modes: I, I, I, O
--------------------------------------------------------------------------------

substTy :: SystemFRel rel => Judgment4 rel "substTy" '[I, I, I, O] TyNom Ty Ty Ty
substTy = defJudge4 @"substTy" $ \rule ->
  [ rule "subst" $ do
      (alpha, tyArg, tyBody, result) <- fresh4
      concl $ substTy alpha tyArg tyBody result
      liftRelDeferred $ substo (tTerm alpha) (tTerm tyBody) (tTerm tyArg) (tTerm result)
  ]

--------------------------------------------------------------------------------
-- Mode-checked typeof: typeof ctx e ty
-- Modes: I, I, O
--------------------------------------------------------------------------------

typeof :: SystemFRel rel => Judgment3 rel "typeof" '[I, I, O] Ctx Tm Ty
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
    --              ← typeof ctx e (forall alpha. tyBody) ∧ [tyArg/alpha]tyBody = result
    rule "typeof-tapp" $ do
      (ctx, e, tyArg, alpha, tyBody, result) <- fresh6
      prem $ typeof ctx e (tall (bindTyPat alpha tyBody))
      prem $ substTy alpha tyArg tyBody result
      concl $ typeof ctx (tapp e tyArg) result
  ]
