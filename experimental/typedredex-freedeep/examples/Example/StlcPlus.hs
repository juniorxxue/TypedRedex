{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}

module Example.StlcPlus
  ( Ty(..)
  , Tm(..)
  , Ctx(..)
  , tunit
  , tint
  , tarr
  , var
  , lam
  , app
  , unit
  , intLit
  , add
  , ctxEmpty
  , ctxCons
  , lookupCtx
  , inferExp
  , infer
  , lamAdd1
  ) where

import TypedRedex.DSL hiding (var)
import qualified TypedRedex.DSL as R
import TypedRedex.Pretty (Pretty(..), (<+>), parens, prettyLogic)
import Support.Nat

--------------------------------------------------------------------------------
-- Syntax
--------------------------------------------------------------------------------

data Ty
  = TyUnit
  | TyArr Ty Ty
  | TyInt
  deriving (Eq, Show)

data Tm
  = TmVar Nat
  | TmLam Ty Tm
  | TmApp Tm Tm
  | TmUnit
  | TmInt Nat
  | TmAdd Tm Tm
  deriving (Eq, Show)

data Ctx
  = CEmpty
  | CCons Ty Ctx
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Repr instances
--------------------------------------------------------------------------------

instance Repr Ty where
  data Reified Ty = RTUnit | RTArr (Logic Ty) (Logic Ty) | RTInt

  project TyUnit = RTUnit
  project (TyArr a b) = RTArr (Ground (project a)) (Ground (project b))
  project TyInt = RTInt

  reify RTUnit = Just TyUnit
  reify (RTArr (Ground a) (Ground b)) = TyArr <$> reify a <*> reify b
  reify RTInt = Just TyInt
  reify _ = Nothing

  quote RTUnit = ("Unit", [])
  quote (RTArr a b) = ("Arr", [Field a, Field b])
  quote RTInt = ("Int", [])

  mapReified _ RTUnit = RTUnit
  mapReified f (RTArr a b) = RTArr (f a) (f b)
  mapReified _ RTInt = RTInt

instance Repr Tm where
  data Reified Tm
    = RVar (Logic Nat)
    | RLam (Logic Ty) (Logic Tm)
    | RApp (Logic Tm) (Logic Tm)
    | RUnit
    | RInt (Logic Nat)
    | RAdd (Logic Tm) (Logic Tm)

  project (TmVar x) = RVar (Ground (project x))
  project (TmLam ty body) = RLam (Ground (project ty)) (Ground (project body))
  project (TmApp t1 t2) = RApp (Ground (project t1)) (Ground (project t2))
  project TmUnit = RUnit
  project (TmInt n) = RInt (Ground (project n))
  project (TmAdd t1 t2) = RAdd (Ground (project t1)) (Ground (project t2))

  reify (RVar (Ground x)) = TmVar <$> reify x
  reify (RLam (Ground ty) (Ground body)) = TmLam <$> reify ty <*> reify body
  reify (RApp (Ground t1) (Ground t2)) = TmApp <$> reify t1 <*> reify t2
  reify RUnit = Just TmUnit
  reify (RInt (Ground n)) = TmInt <$> reify n
  reify (RAdd (Ground t1) (Ground t2)) = TmAdd <$> reify t1 <*> reify t2
  reify _ = Nothing

  quote (RVar x) = ("Var", [Field x])
  quote (RLam ty body) = ("Lam", [Field ty, Field body])
  quote (RApp t1 t2) = ("App", [Field t1, Field t2])
  quote RUnit = ("Unit", [])
  quote (RInt n) = ("Int", [Field n])
  quote (RAdd t1 t2) = ("Add", [Field t1, Field t2])

  mapReified f (RVar x) = RVar (f x)
  mapReified f (RLam ty body) = RLam (f ty) (f body)
  mapReified f (RApp t1 t2) = RApp (f t1) (f t2)
  mapReified _ RUnit = RUnit
  mapReified f (RInt n) = RInt (f n)
  mapReified f (RAdd t1 t2) = RAdd (f t1) (f t2)

instance Repr Ctx where
  data Reified Ctx = REmpty | RCons (Logic Ty) (Logic Ctx)

  project CEmpty = REmpty
  project (CCons ty ctx) = RCons (Ground (project ty)) (Ground (project ctx))

  reify REmpty = Just CEmpty
  reify (RCons (Ground ty) (Ground ctx)) = CCons <$> reify ty <*> reify ctx
  reify _ = Nothing

  quote REmpty = ("Empty", [])
  quote (RCons ty ctx) = ("Cons", [Field ty, Field ctx])

  mapReified _ REmpty = REmpty
  mapReified f (RCons ty ctx) = RCons (f ty) (f ctx)

--------------------------------------------------------------------------------
-- Pretty instances
--------------------------------------------------------------------------------

instance Pretty Ty where
  prettyReified RTUnit = pure "Unit"
  prettyReified RTInt = pure "Int"
  prettyReified (RTArr a b) = do
    da <- prettyLogic a
    db <- prettyLogic b
    pure (parens (da <+> " -> " <+> db))

instance Pretty Tm where
  prettyReified (RVar x) = do
    dx <- prettyLogic x
    pure ("x" <+> dx)
  prettyReified (RLam ty body) = do
    dty <- prettyLogic ty
    dbody <- prettyLogic body
    pure ("\\x:" <+> dty <+> ". " <+> dbody)
  prettyReified (RApp t1 t2) = do
    d1 <- prettyLogic t1
    d2 <- prettyLogic t2
    pure (parens (d1 <+> " " <+> d2))
  prettyReified RUnit = pure "unit"
  prettyReified (RInt n) = prettyLogic n
  prettyReified (RAdd t1 t2) = do
    d1 <- prettyLogic t1
    d2 <- prettyLogic t2
    pure (d1 <+> " + " <+> d2)

instance Pretty Ctx where
  prettyReified REmpty = pure "."
  prettyReified (RCons ty ctx) = do
    dty <- prettyLogic ty
    dctx <- prettyLogic ctx
    pure (dctx <+> ", " <+> dty)

--------------------------------------------------------------------------------
-- Smart constructors
--------------------------------------------------------------------------------

tunit :: Term Ty
tunit = ground TyUnit

tint :: Term Ty
tint = ground TyInt

tarr :: Term Ty -> Term Ty -> Term Ty
tarr = lift2 (\a b -> Ground (RTArr a b))

var :: Term Nat -> Term Tm
var = lift1 (\n -> Ground (RVar n))

lam :: Term Ty -> Term Tm -> Term Tm
lam = lift2 (\ty body -> Ground (RLam ty body))

app :: Term Tm -> Term Tm -> Term Tm
app = lift2 (\t1 t2 -> Ground (RApp t1 t2))

unit :: Term Tm
unit = ground TmUnit

intLit :: Term Nat -> Term Tm
intLit = lift1 (\n -> Ground (RInt n))

add :: Term Tm -> Term Tm -> Term Tm
add = lift2 (\t1 t2 -> Ground (RAdd t1 t2))

ctxEmpty :: Term Ctx
ctxEmpty = ground CEmpty

ctxCons :: Term Ty -> Term Ctx -> Term Ctx
ctxCons = lift2 (\ty ctx -> Ground (RCons ty ctx))

--------------------------------------------------------------------------------
-- Judgments
--------------------------------------------------------------------------------

lookupCtx :: Judgment "lookup+" '[I, I, O] '[Ctx, Nat, Ty]
lookupCtx = judgment $ do
  format $ \ctx x ty -> ctx <+> "[" <+> x <+> "]" <+> " = " <+> ty
  rules
    [ rule "lookup-here" $ R.do
        (ty, ctx) <- R.fresh
        R.concl $ lookupCtx (ctxCons ty ctx) zro ty

    , rule "lookup-there" $ R.do
        (ty, ctx, n, tyOut) <- R.fresh
        R.concl $ lookupCtx (ctxCons ty ctx) (suc n) tyOut
        R.prem  $ lookupCtx ctx n tyOut
    ]

inferExp :: Judgment "inferExp+" '[I, I, O] '[Ctx, Tm, Ty]
inferExp = judgment $ do
  format $ \ctx tm ty -> ctx <+> " |- " <+> tm <+> " : " <+> ty
  rules
    [ rule "infer-add" $ R.do
        (ctx, t1, t2) <- R.fresh
        R.concl $ inferExp ctx (add t1 t2) tint
        R.prem  $ inferExp ctx t1 tint
        R.prem  $ inferExp ctx t2 tint

    , rule "infer-app" $ R.do
        (ctx, fun, arg, argTy, resTy) <- R.fresh
        R.concl $ inferExp ctx (app fun arg) resTy
        R.prem  $ inferExp ctx fun (tarr argTy resTy)
        R.prem  $ inferExp ctx arg argTy

    , rule "infer-var" $ R.do
        (ctx, x, ty) <- R.fresh
        R.concl $ inferExp ctx (var x) ty
        R.prem  $ lookupCtx ctx x ty

    , rule "infer-unit" $ R.do
        ctx <- R.fresh
        R.concl $ inferExp ctx unit tunit

    , rule "infer-int" $ R.do
        (ctx, n) <- R.fresh
        R.concl $ inferExp ctx (intLit n) tint
    ]

infer :: Judgment "infer+" '[I, I, O] '[Ctx, Tm, Ty]
infer = judgment $ do
  format $ \ctx tm ty -> ctx <+> " |- " <+> tm <+> " : " <+> ty
  rules
    [ rule "infer-lam" $ R.do
        (ctx, argTy, body, bodyTy) <- R.fresh
        R.concl $ infer ctx (lam argTy body) (tarr argTy bodyTy)
        R.prem  $ inferExp (ctxCons argTy ctx) body bodyTy

    , rule "infer-exp" $ R.do
        (ctx, tm, ty) <- R.fresh
        R.concl $ infer ctx tm ty
        R.prem  $ inferExp ctx tm ty
    ]

--------------------------------------------------------------------------------
-- Sample terms
--------------------------------------------------------------------------------

lamAdd1 :: Term Tm
lamAdd1 =
  lam tint (add (var zro) unit)
