{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RebindableSyntax #-}

module SystemFNominal.Rules
  ( lookupVar
  , tySubst
  , tyEquiv
  , infer
  , idTm
  , idTy
  ) where

import Data.String (fromString)
import Prelude hiding ((>>=), (>>), return)
import qualified Prelude as P
import TypedRedex.DSL hiding (var)
import TypedRedex.Nominal.Bind (bind)
import TypedRedex.Nominal.Prelude (Nom, TyNom, freshTyNom, nom, tynom, unbind2)
import TypedRedex.Pretty ((<+>))

import SystemFNominal.Syntax

--------------------------------------------------------------------------------
-- Judgments
--------------------------------------------------------------------------------

lookupVar :: Judgment "lookupVar" '[I, I, O] '[Ctx, Nom, Ty]
lookupVar = judgment $
  format (\ctx x ty -> ctx <+> " |- " <+> x <+> " : " <+> ty)
  P.>> rules
    [ rule "lookup-here" $ do
        (x, ty, ctx) <- fresh
        concl $ lookupVar (ctxVar x ty ctx) x ty

    , rule "lookup-skip" $ do
        (x, y, ty, ty', ctx) <- fresh
        x =/= y
        prem  $ lookupVar ctx x ty
        concl $ lookupVar (ctxVar y ty' ctx) x ty

    , rule "lookup-ty" $ do
        (x, a, ty, ctx) <- fresh
        prem  $ lookupVar ctx x ty
        concl $ lookupVar (ctxTy a ctx) x ty
    ]

tySubst :: Judgment "tySubst" '[I, I, I, O] '[Ty, TyNom, Ty, Ty]
tySubst = judgment $
  format (\body a repl res -> "[" <+> repl <+> "/" <+> a <+> "]" <+> body <+> " = " <+> res)
  P.>> rules
    [ rule "subst-unit" $ do
        (a, ty) <- fresh
        concl $ tySubst tunit a ty tunit

    , rule "subst-int" $ do
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
        (a, b, body, ty, body', body'') <- fresh
        bFresh <- freshTyNom
        concl $ tySubst (tforall b body) a ty (tforall bFresh body'')
        a =/= b
        hash bFresh ty
        (bind b body) === (bind bFresh body')
        prem  $ tySubst body' a ty body''
    ]

tyEquiv :: Judgment "tyEquiv" '[I, I] '[Ty, Ty]
tyEquiv = judgment $
  format (\t1 t2 -> t1 <+> " === " <+> t2)
  P.>> rules
    [ rule "equiv-unit" $ do
        concl $ tyEquiv tunit tunit

    , rule "equiv-int" $ do
        concl $ tyEquiv tint tint

    , rule "equiv-var" $ do
        a <- fresh
        concl $ tyEquiv (tvar a) (tvar a)

    , rule "equiv-arr" $ do
        (a1, a2, b1, b2) <- fresh
        concl $ tyEquiv (tarr a1 a2) (tarr b1 b2)
        prem  $ tyEquiv a1 b1
        prem  $ tyEquiv a2 b2

    , rule "equiv-forall" $ do
        (a, b, body, body') <- fresh
        (_x, body1, body2) <- unbind2 (bind a body) (bind b body')
        concl $ tyEquiv (tforall a body) (tforall b body')
        prem  $ tyEquiv body1 body2
    ]

infer :: Judgment "infer" '[I, I, O] '[Ctx, Tm, Ty]
infer = judgment $
  format (\ctx tm ty -> ctx <+> " |- " <+> tm <+> " : " <+> ty)
  P.>> rules
    [ rule "infer-var" $ do
        (ctx, x, ty) <- fresh
        concl $ infer ctx (var x) ty
        prem  $ lookupVar ctx x ty

    , rule "infer-int" $ do
        (ctx, n) <- fresh
        concl $ infer ctx (intLit n) tint

    , rule "infer-lam" $ do
        (ctx, x, argTy, body, bodyTy) <- fresh
        concl $ infer ctx (lam argTy x body) (tarr argTy bodyTy)
        prem  $ infer (ctxVar x argTy ctx) body bodyTy

    , rule "infer-app" $ do
        (ctx, t1, t2, argTy, resTy) <- fresh
        concl $ infer ctx (app t1 t2) resTy
        prem  $ infer ctx t1 (tarr argTy resTy)
        prem  $ infer ctx t2 argTy

    , rule "infer-tlam" $ do
        (ctx, a, body, bodyTy) <- fresh
        concl $ infer ctx (tlam a body) (tforall a bodyTy)
        prem  $ infer (ctxTy a ctx) body bodyTy

    , rule "infer-tapp" $ do
        (ctx, tm, a, bodyTy, argTy, resTy) <- fresh
        concl $ infer ctx (tapp tm argTy) resTy
        prem  $ infer ctx tm (tforall a bodyTy)
        prem  $ tySubst bodyTy a argTy resTy
    ]

--------------------------------------------------------------------------------
-- Sample terms
--------------------------------------------------------------------------------

idTm :: Term Tm
idTm =
  tlam (tynom 0) (lam (tvar (tynom 0)) (nom 0) (var (nom 0)))

idTy :: Term Ty
idTy =
  tforall (tynom 0) (tarr (tvar (tynom 0)) (tvar (tynom 0)))
