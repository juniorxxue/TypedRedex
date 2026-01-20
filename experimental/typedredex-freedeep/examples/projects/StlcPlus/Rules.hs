{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RebindableSyntax #-}

module StlcPlus.Rules
  ( lookupCtx
  , inferExp
  , infer
  , lamAdd1
  ) where

import Data.String (fromString)
import Prelude hiding ((>>=), (>>), return)
import qualified Prelude as P
import TypedRedex.DSL hiding (var)
import TypedRedex.Pretty ((<+>))

import StlcPlus.Syntax
import Support.Nat (Nat, zro, suc)

--------------------------------------------------------------------------------
-- Judgments
--------------------------------------------------------------------------------

lookupCtx :: Judgment "lookup+" '[I, I, O] '[Ctx, Nat, Ty]
lookupCtx = judgment $
  format (\ctx x ty -> ctx <+> "[" <+> x <+> "] = " <+> ty)
  P.>> rules
    [ rule "lookup-here" $ do
        (ty, ctx) <- fresh
        concl $ lookupCtx (ctxCons ty ctx) zro ty

    , rule "lookup-there" $ do
        (ty, ctx, n, tyOut) <- fresh
        concl $ lookupCtx (ctxCons ty ctx) (suc n) tyOut
        prem  $ lookupCtx ctx n tyOut
    ]

inferExp :: Judgment "inferExp+" '[I, I, O] '[Ctx, Tm, Ty]
inferExp = judgment $
  format (\ctx tm ty -> ctx <+> " |- " <+> tm <+> " : " <+> ty)
  P.>> rules
    [ rule "infer-add" $ do
        (ctx, t1, t2) <- fresh
        concl $ inferExp ctx (add t1 t2) tint
        prem  $ inferExp ctx t1 tint
        prem  $ inferExp ctx t2 tint

    , rule "infer-app" $ do
        (ctx, fun, arg, argTy, resTy) <- fresh
        concl $ inferExp ctx (app fun arg) resTy
        prem  $ inferExp ctx fun (tarr argTy resTy)
        prem  $ inferExp ctx arg argTy

    , rule "infer-var" $ do
        (ctx, x, ty) <- fresh
        concl $ inferExp ctx (var x) ty
        prem  $ lookupCtx ctx x ty

    , rule "infer-unit" $ do
        ctx <- fresh
        concl $ inferExp ctx unit tunit

    , rule "infer-int" $ do
        (ctx, n) <- fresh
        concl $ inferExp ctx (intLit n) tint
    ]

infer :: Judgment "infer+" '[I, I, O] '[Ctx, Tm, Ty]
infer = judgment $
  format (\ctx tm ty -> ctx <+> " |- " <+> tm <+> " : " <+> ty)
  P.>> rules
    [ rule "infer-lam" $ do
        (ctx, argTy, body, bodyTy) <- fresh
        concl $ infer ctx (lam argTy body) (tarr argTy bodyTy)
        prem  $ inferExp (ctxCons argTy ctx) body bodyTy

    , rule "infer-exp" $ do
        (ctx, tm, ty) <- fresh
        concl $ infer ctx tm ty
        prem  $ inferExp ctx tm ty
    ]

--------------------------------------------------------------------------------
-- Sample terms
--------------------------------------------------------------------------------

lamAdd1 :: Term Tm
lamAdd1 =
  lam tint (add (var zro) unit)
