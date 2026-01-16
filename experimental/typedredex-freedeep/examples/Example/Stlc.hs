{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE TypeFamilies #-}

module Example.Stlc
  ( Ty(..)
  , Tm(..)
  , Ctx(..)
  , tunit
  , tarr
  , var
  , lam
  , app
  , unit
  , ctxEmpty
  , ctxCons
  , lookupCtx
  , infer
  , idUnit
  , appIdUnit
  ) where

import TypedRedex.DSL hiding (var)
import qualified TypedRedex.DSL as R
import Support.Nat

--------------------------------------------------------------------------------
-- Syntax
--------------------------------------------------------------------------------

data Ty
  = TyUnit
  | TyArr Ty Ty
  deriving (Eq, Show)

data Tm
  = TmVar Nat
  | TmLam Ty Tm
  | TmApp Tm Tm
  | TmUnit
  deriving (Eq, Show)

data Ctx
  = CEmpty
  | CCons Ty Ctx
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Repr instances
--------------------------------------------------------------------------------

instance Repr Ty where
  data Reified Ty = RTUnit | RTArr (Logic Ty) (Logic Ty)

  project TyUnit = RTUnit
  project (TyArr a b) = RTArr (Ground (project a)) (Ground (project b))

  reify RTUnit = Just TyUnit
  reify (RTArr (Ground a) (Ground b)) = TyArr <$> reify a <*> reify b
  reify _ = Nothing

  quote RTUnit = ("Unit", [])
  quote (RTArr a b) = ("Arr", [Field a, Field b])

  mapReified _ RTUnit = RTUnit
  mapReified f (RTArr a b) = RTArr (f a) (f b)

instance Repr Tm where
  data Reified Tm
    = RVar (Logic Nat)
    | RLam (Logic Ty) (Logic Tm)
    | RApp (Logic Tm) (Logic Tm)
    | RUnit

  project (TmVar x) = RVar (Ground (project x))
  project (TmLam ty body) = RLam (Ground (project ty)) (Ground (project body))
  project (TmApp t1 t2) = RApp (Ground (project t1)) (Ground (project t2))
  project TmUnit = RUnit

  reify (RVar (Ground x)) = TmVar <$> reify x
  reify (RLam (Ground ty) (Ground body)) = TmLam <$> reify ty <*> reify body
  reify (RApp (Ground t1) (Ground t2)) = TmApp <$> reify t1 <*> reify t2
  reify RUnit = Just TmUnit
  reify _ = Nothing

  quote (RVar x) = ("Var", [Field x])
  quote (RLam ty body) = ("Lam", [Field ty, Field body])
  quote (RApp t1 t2) = ("App", [Field t1, Field t2])
  quote RUnit = ("Unit", [])

  mapReified f (RVar x) = RVar (f x)
  mapReified f (RLam ty body) = RLam (f ty) (f body)
  mapReified f (RApp t1 t2) = RApp (f t1) (f t2)
  mapReified _ RUnit = RUnit

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
-- Smart constructors
--------------------------------------------------------------------------------

tunit :: Term Ty
tunit = ground TyUnit

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

ctxEmpty :: Term Ctx
ctxEmpty = ground CEmpty

ctxCons :: Term Ty -> Term Ctx -> Term Ctx
ctxCons = lift2 (\ty ctx -> Ground (RCons ty ctx))

--------------------------------------------------------------------------------
-- Judgments
--------------------------------------------------------------------------------

lookupCtx :: Judgment "lookup" '[I, I, O] '[Ctx, Nat, Ty]
lookupCtx = judgment
  [ rule "lookup-here" $ R.do
      ty <- R.fresh
      ctx <- R.fresh
      R.concl $ lookupCtx (ctxCons ty ctx) zro ty

  , rule "lookup-there" $ R.do
      ty <- R.fresh
      ctx <- R.fresh
      n <- R.fresh
      tyOut <- R.fresh
      R.concl $ lookupCtx (ctxCons ty ctx) (suc n) tyOut
      R.prem  $ lookupCtx ctx n tyOut
  ]

infer :: Judgment "infer" '[I, I, O] '[Ctx, Tm, Ty]
infer = judgment
  [ rule "infer-var" $ R.do
      ctx <- R.fresh
      x <- R.fresh
      ty <- R.fresh
      R.concl $ infer ctx (var x) ty
      R.prem  $ lookupCtx ctx x ty

  , rule "infer-unit" $ R.do
      ctx <- R.fresh
      R.concl $ infer ctx unit tunit

  , rule "infer-lam" $ R.do
      ctx <- R.fresh
      argTy <- R.fresh
      body <- R.fresh
      bodyTy <- R.fresh
      R.concl $ infer ctx (lam argTy body) (tarr argTy bodyTy)
      R.prem  $ infer (ctxCons argTy ctx) body bodyTy

  , rule "infer-app" $ R.do
      ctx <- R.fresh
      fun <- R.fresh
      arg <- R.fresh
      argTy <- R.fresh
      resTy <- R.fresh
      R.concl $ infer ctx (app fun arg) resTy
      R.prem  $ infer ctx fun (tarr argTy resTy)
      R.prem  $ infer ctx arg argTy
  ]

--------------------------------------------------------------------------------
-- Sample terms
--------------------------------------------------------------------------------

idUnit :: Term Tm
idUnit = lam tunit (var zro)

appIdUnit :: Term Tm
appIdUnit = app idUnit unit
