{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE TypeFamilies #-}

module Example.Poly
  ( Ty(..)
  , Tm(..)
  , Ctx(..)
  , tint
  , tvar
  , tarr
  , tforall
  , var
  , lam
  , app
  , tlam
  , tapp
  , cempty
  , cbind
  , lookupCtx
  , tySubst
  , infer
  , polyId
  , polyIdTy
  , polyIdApp
  , polyIdAppTy
  ) where

import TypedRedex.DSL hiding (var)
import qualified TypedRedex.DSL as R
import Support.Nat

--------------------------------------------------------------------------------
-- Syntax
--------------------------------------------------------------------------------

data Ty
  = TyInt
  | TyVar Nat
  | TyArr Ty Ty
  | TyForall Nat Ty
  deriving (Eq, Show)

data Tm
  = TmVar Nat
  | TmLam Nat Ty Tm
  | TmApp Tm Tm
  | TmTLam Nat Tm
  | TmTApp Tm Ty
  deriving (Eq, Show)

data Ctx
  = CEmpty
  | CBind Nat Ty Ctx
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Repr instances
--------------------------------------------------------------------------------

instance Repr Ty where
  data Reified Ty
    = RTInt
    | RTVar (Logic Nat)
    | RTArr (Logic Ty) (Logic Ty)
    | RTForall (Logic Nat) (Logic Ty)

  project TyInt = RTInt
  project (TyVar a) = RTVar (Ground (project a))
  project (TyArr a b) = RTArr (Ground (project a)) (Ground (project b))
  project (TyForall a body) = RTForall (Ground (project a)) (Ground (project body))

  reify RTInt = Just TyInt
  reify (RTVar (Ground a)) = TyVar <$> reify a
  reify (RTArr (Ground a) (Ground b)) = TyArr <$> reify a <*> reify b
  reify (RTForall (Ground a) (Ground body)) = TyForall <$> reify a <*> reify body
  reify _ = Nothing

  quote RTInt = ("Int", [])
  quote (RTVar a) = ("Var", [Field a])
  quote (RTArr a b) = ("Arr", [Field a, Field b])
  quote (RTForall a body) = ("Forall", [Field a, Field body])

  mapReified _ RTInt = RTInt
  mapReified f (RTVar a) = RTVar (f a)
  mapReified f (RTArr a b) = RTArr (f a) (f b)
  mapReified f (RTForall a body) = RTForall (f a) (f body)

instance Repr Tm where
  data Reified Tm
    = RVar (Logic Nat)
    | RLam (Logic Nat) (Logic Ty) (Logic Tm)
    | RApp (Logic Tm) (Logic Tm)
    | RTLam (Logic Nat) (Logic Tm)
    | RTApp (Logic Tm) (Logic Ty)

  project (TmVar x) = RVar (Ground (project x))
  project (TmLam x ty body) = RLam (Ground (project x)) (Ground (project ty)) (Ground (project body))
  project (TmApp t1 t2) = RApp (Ground (project t1)) (Ground (project t2))
  project (TmTLam a body) = RTLam (Ground (project a)) (Ground (project body))
  project (TmTApp t ty) = RTApp (Ground (project t)) (Ground (project ty))

  reify (RVar (Ground x)) = TmVar <$> reify x
  reify (RLam (Ground x) (Ground ty) (Ground body)) = TmLam <$> reify x <*> reify ty <*> reify body
  reify (RApp (Ground t1) (Ground t2)) = TmApp <$> reify t1 <*> reify t2
  reify (RTLam (Ground a) (Ground body)) = TmTLam <$> reify a <*> reify body
  reify (RTApp (Ground t) (Ground ty)) = TmTApp <$> reify t <*> reify ty
  reify _ = Nothing

  quote (RVar x) = ("Var", [Field x])
  quote (RLam x ty body) = ("Lam", [Field x, Field ty, Field body])
  quote (RApp t1 t2) = ("App", [Field t1, Field t2])
  quote (RTLam a body) = ("TLam", [Field a, Field body])
  quote (RTApp t ty) = ("TApp", [Field t, Field ty])

  mapReified f (RVar x) = RVar (f x)
  mapReified f (RLam x ty body) = RLam (f x) (f ty) (f body)
  mapReified f (RApp t1 t2) = RApp (f t1) (f t2)
  mapReified f (RTLam a body) = RTLam (f a) (f body)
  mapReified f (RTApp t ty) = RTApp (f t) (f ty)

instance Repr Ctx where
  data Reified Ctx = REmpty | RBind (Logic Nat) (Logic Ty) (Logic Ctx)

  project CEmpty = REmpty
  project (CBind x ty ctx) = RBind (Ground (project x)) (Ground (project ty)) (Ground (project ctx))

  reify REmpty = Just CEmpty
  reify (RBind (Ground x) (Ground ty) (Ground ctx)) = CBind <$> reify x <*> reify ty <*> reify ctx
  reify _ = Nothing

  quote REmpty = ("Empty", [])
  quote (RBind x ty ctx) = ("Bind", [Field x, Field ty, Field ctx])

  mapReified _ REmpty = REmpty
  mapReified f (RBind x ty ctx) = RBind (f x) (f ty) (f ctx)

--------------------------------------------------------------------------------
-- Smart constructors
--------------------------------------------------------------------------------

tint :: Term Ty
tint = ground TyInt

tvar :: Term Nat -> Term Ty
tvar = lift1 (\a -> Ground (RTVar a))

tarr :: Term Ty -> Term Ty -> Term Ty
tarr = lift2 (\a b -> Ground (RTArr a b))

tforall :: Term Nat -> Term Ty -> Term Ty
tforall = lift2 (\a body -> Ground (RTForall a body))

var :: Term Nat -> Term Tm
var = lift1 (\x -> Ground (RVar x))

lam :: Term Nat -> Term Ty -> Term Tm -> Term Tm
lam = lift3 (\x ty body -> Ground (RLam x ty body))

app :: Term Tm -> Term Tm -> Term Tm
app = lift2 (\t1 t2 -> Ground (RApp t1 t2))

tlam :: Term Nat -> Term Tm -> Term Tm
tlam = lift2 (\a body -> Ground (RTLam a body))

tapp :: Term Tm -> Term Ty -> Term Tm
tapp = lift2 (\t ty -> Ground (RTApp t ty))

cempty :: Term Ctx
cempty = ground CEmpty

cbind :: Term Nat -> Term Ty -> Term Ctx -> Term Ctx
cbind = lift3 (\x ty ctx -> Ground (RBind x ty ctx))

--------------------------------------------------------------------------------
-- Judgments
--------------------------------------------------------------------------------

lookupCtx :: Judgment "lookup" '[I, I, O] '[Ctx, Nat, Ty]
lookupCtx = judgment
  [ rule "lookup-here" $ R.do
      x <- R.fresh
      ty <- R.fresh
      ctx <- R.fresh
      R.concl $ lookupCtx (cbind x ty ctx) x ty

  , rule "lookup-there" $ R.do
      x <- R.fresh
      y <- R.fresh
      ty <- R.fresh
      tyOut <- R.fresh
      ctx <- R.fresh
      R.concl $ lookupCtx (cbind y ty ctx) x tyOut
      R.prem  $ lookupCtx ctx x tyOut
      x =/= y
  ]

tySubst :: Judgment "tySubst" '[I, I, I, O] '[Ty, Nat, Ty, Ty]
tySubst = judgment
  [ rule "subst-int" $ R.do
      a <- R.fresh
      ty <- R.fresh
      R.concl $ tySubst tint a ty tint

  , rule "subst-var-hit" $ R.do
      a <- R.fresh
      ty <- R.fresh
      R.concl $ tySubst (tvar a) a ty ty

  , rule "subst-var-miss" $ R.do
      a <- R.fresh
      b <- R.fresh
      ty <- R.fresh
      R.concl $ tySubst (tvar b) a ty (tvar b)
      a =/= b

  , rule "subst-arr" $ R.do
      t1 <- R.fresh
      t2 <- R.fresh
      a <- R.fresh
      ty <- R.fresh
      r1 <- R.fresh
      r2 <- R.fresh
      R.concl $ tySubst (tarr t1 t2) a ty (tarr r1 r2)
      R.prem  $ tySubst t1 a ty r1
      R.prem  $ tySubst t2 a ty r2

  , rule "subst-forall-shadow" $ R.do
      a <- R.fresh
      body <- R.fresh
      ty <- R.fresh
      R.concl $ tySubst (tforall a body) a ty (tforall a body)

  , rule "subst-forall" $ R.do
      a <- R.fresh
      b <- R.fresh
      body <- R.fresh
      ty <- R.fresh
      body' <- R.fresh
      R.concl $ tySubst (tforall b body) a ty (tforall b body')
      R.prem  $ tySubst body a ty body'
      a =/= b
  ]

infer :: Judgment "infer" '[I, I, O] '[Ctx, Tm, Ty]
infer = judgment
  [ rule "infer-var" $ R.do
      ctx <- R.fresh
      x <- R.fresh
      ty <- R.fresh
      R.concl $ infer ctx (var x) ty
      R.prem  $ lookupCtx ctx x ty

  , rule "infer-lam" $ R.do
      ctx <- R.fresh
      x <- R.fresh
      argTy <- R.fresh
      body <- R.fresh
      bodyTy <- R.fresh
      R.concl $ infer ctx (lam x argTy body) (tarr argTy bodyTy)
      R.prem  $ infer (cbind x argTy ctx) body bodyTy

  , rule "infer-app" $ R.do
      ctx <- R.fresh
      fun <- R.fresh
      arg <- R.fresh
      argTy <- R.fresh
      resTy <- R.fresh
      R.concl $ infer ctx (app fun arg) resTy
      R.prem  $ infer ctx fun (tarr argTy resTy)
      R.prem  $ infer ctx arg argTy

  , rule "infer-tlam" $ R.do
      ctx <- R.fresh
      a <- R.fresh
      body <- R.fresh
      bodyTy <- R.fresh
      R.concl $ infer ctx (tlam a body) (tforall a bodyTy)
      R.prem  $ infer ctx body bodyTy

  , rule "infer-tapp" $ R.do
      ctx <- R.fresh
      tm <- R.fresh
      a <- R.fresh
      bodyTy <- R.fresh
      argTy <- R.fresh
      resTy <- R.fresh
      R.concl $ infer ctx (tapp tm argTy) resTy
      R.prem  $ infer ctx tm (tforall a bodyTy)
      R.prem  $ tySubst bodyTy a argTy resTy
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
