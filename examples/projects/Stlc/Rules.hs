{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RebindableSyntax #-}

module Stlc.Rules
  ( lookupCtx
  , infer
  , idUnit
  , appIdUnit
  ) where

import Data.String (fromString)
import Prelude hiding ((>>=), (>>), return)
import qualified Prelude as P
import TypedRedex.DSL hiding (var)
import TypedRedex.Pretty ((<+>))

import Stlc.Syntax
import Support.Nat (Nat, zro, suc)

--------------------------------------------------------------------------------
-- Judgments
--------------------------------------------------------------------------------

lookupCtx :: Judgment "lookup" '[I, I, O] '[Ctx, Nat, Ty]
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

infer :: Judgment "infer" '[I, I, O] '[Ctx, Tm, Ty]
infer = judgment $
  format (\ctx tm ty -> ctx <+> " |- " <+> tm <+> " : " <+> ty)
  P.>> rules
    [ rule "infer-var" $ do
        (ctx, x, ty) <- fresh
        concl $ infer ctx (var x) ty
        prem  $ lookupCtx ctx x ty

    , rule "infer-unit" $ do
        ctx <- fresh
        concl $ infer ctx unit tunit

    , rule "infer-lam" $ do
        (ctx, argTy, body, bodyTy) <- fresh
        concl $ infer ctx (lam argTy body) (tarr argTy bodyTy)
        prem  $ infer (ctxCons argTy ctx) body bodyTy

    , rule "infer-app" $ do
        (ctx, fun, arg, argTy, resTy) <- fresh
        concl $ infer ctx (app fun arg) resTy
        prem  $ infer ctx fun (tarr argTy resTy)
        prem  $ infer ctx arg argTy
    ]

--------------------------------------------------------------------------------
-- Sample terms
--------------------------------------------------------------------------------

idUnit :: Term Tm
idUnit = lam tunit (var zro)

appIdUnit :: Term Tm
appIdUnit = app idUnit unit
