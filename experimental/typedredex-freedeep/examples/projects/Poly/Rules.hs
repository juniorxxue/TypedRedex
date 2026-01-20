{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RebindableSyntax #-}

module Poly.Rules
  ( lookupCtx
  , tySubst
  , infer
  , polyId
  , polyIdTy
  , polyIdApp
  , polyIdAppTy
  ) where

import Prelude hiding ((>>=), (>>), return)
import TypedRedex.DSL hiding (var)

import Poly.Syntax
import Support.Nat (Nat, zro, suc)

--------------------------------------------------------------------------------
-- Judgments
--------------------------------------------------------------------------------

lookupCtx :: Judgment "lookup" '[I, I, O] '[Ctx, Nat, Ty]
lookupCtx = judgment
  [ rule "lookup-here" $ do
      (x, ty, ctx) <- fresh
      concl $ lookupCtx (cbind x ty ctx) x ty

  , rule "lookup-there" $ do
      (x, y, ty, tyOut, ctx) <- fresh
      concl $ lookupCtx (cbind y ty ctx) x tyOut
      prem  $ lookupCtx ctx x tyOut
      x =/= y
  ]

tySubst :: Judgment "tySubst" '[I, I, I, O] '[Ty, Nat, Ty, Ty]
tySubst = judgment
  [ rule "subst-int" $ do
      (a, ty) <- fresh
      concl $ tySubst tint a ty tint

  , rule "subst-var-hit" $ do
      (a, ty) <- fresh
      concl $ tySubst (tvar a) a ty ty

  , rule "subst-var-miss" $ do
      (a, b, ty) <- fresh
      concl $ tySubst (tvar b) a ty (tvar b)
      a =/= b

  , rule "subst-arr" $ do
      (t1, t2, a, ty, r1, r2) <- fresh
      concl $ tySubst (tarr t1 t2) a ty (tarr r1 r2)
      prem  $ tySubst t1 a ty r1
      prem  $ tySubst t2 a ty r2

  , rule "subst-forall-shadow" $ do
      (a, body, ty) <- fresh
      concl $ tySubst (tforall a body) a ty (tforall a body)

  , rule "subst-forall" $ do
      (a, b, body, ty, body') <- fresh
      concl $ tySubst (tforall b body) a ty (tforall b body')
      prem  $ tySubst body a ty body'
      a =/= b
  ]

infer :: Judgment "infer" '[I, I, O] '[Ctx, Tm, Ty]
infer = judgment
  [ rule "infer-var" $ do
      (ctx, x, ty) <- fresh
      concl $ infer ctx (var x) ty
      prem  $ lookupCtx ctx x ty

  , rule "infer-lam" $ do
      (ctx, x, argTy, body, bodyTy) <- fresh
      concl $ infer ctx (lam x argTy body) (tarr argTy bodyTy)
      prem  $ infer (cbind x argTy ctx) body bodyTy

  , rule "infer-app" $ do
      (ctx, fun, arg, argTy, resTy) <- fresh
      concl $ infer ctx (app fun arg) resTy
      prem  $ infer ctx fun (tarr argTy resTy)
      prem  $ infer ctx arg argTy

  , rule "infer-tlam" $ do
      (ctx, a, body, bodyTy) <- fresh
      concl $ infer ctx (tlam a body) (tforall a bodyTy)
      prem  $ infer ctx body bodyTy

  , rule "infer-tapp" $ do
      (ctx, tm, a, bodyTy, argTy, resTy) <- fresh
      concl $ infer ctx (tapp tm argTy) resTy
      prem  $ infer ctx tm (tforall a bodyTy)
      prem  $ tySubst bodyTy a argTy resTy
  ]

--------------------------------------------------------------------------------
-- Sample terms
--------------------------------------------------------------------------------

polyId :: Term Tm
polyId =
  let a = zro
      x = suc zro
  in tlam a (lam x (tvar a) (var x))

polyIdTy :: Term Ty
polyIdTy =
  let a = zro
  in tforall a (tarr (tvar a) (tvar a))

polyIdApp :: Term Tm
polyIdApp = tapp polyId tint

polyIdAppTy :: Term Ty
polyIdAppTy = tarr tint tint
