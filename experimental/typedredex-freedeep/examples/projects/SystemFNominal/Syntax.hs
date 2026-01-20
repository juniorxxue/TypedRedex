{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module SystemFNominal.Syntax
  ( Ty(..)
  , Tm(..)
  , Ctx(..)
  , tunit
  , tint
  , tvar
  , tarr
  , tforall
  , var
  , lam
  , app
  , intLit
  , tlam
  , tapp
  , ctxEmpty
  , ctxVar
  , ctxTy
  ) where

import TypedRedex.Core.Term hiding (var)
import TypedRedex.Nominal (NominalAtom, Permute(..), Hash(..))
import TypedRedex.Nominal.Bind (Bind(..), bind, unbind)
import TypedRedex.Nominal.Prelude (Nom, TyNom)
import TypedRedex.Pretty (Pretty(..), PrettyM, Doc(..), (<+>), parens, prettyLogic, cycleNames)
import Support.Nat

--------------------------------------------------------------------------------
-- Syntax
--------------------------------------------------------------------------------

data Ty
  = TyUnit
  | TyInt
  | TyVar TyNom
  | TyArr Ty Ty
  | TyForall (Bind TyNom Ty)
  deriving (Eq, Show)

data Tm
  = TmVar Nom
  | TmLam Ty (Bind Nom Tm)
  | TmApp Tm Tm
  | TmInt Nat
  | TmTAbs (Bind TyNom Tm)
  | TmTApp Tm Ty
  deriving (Eq, Show)

data Ctx
  = CEmpty
  | CVar Nom Ty Ctx
  | CTy TyNom Ctx
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Repr instances
--------------------------------------------------------------------------------

instance Repr Ty where
  data Reified Ty
    = RTUnit
    | RTInt
    | RTVar (Logic TyNom)
    | RTArr (Logic Ty) (Logic Ty)
    | RTForall (Logic (Bind TyNom Ty))

  project TyUnit = RTUnit
  project TyInt = RTInt
  project (TyVar a) = RTVar (Ground (project a))
  project (TyArr a b) = RTArr (Ground (project a)) (Ground (project b))
  project (TyForall bnd) = RTForall (Ground (project bnd))

  reify RTUnit = Just TyUnit
  reify RTInt = Just TyInt
  reify (RTVar (Ground a)) = TyVar <$> reify a
  reify (RTArr (Ground a) (Ground b)) = TyArr <$> reify a <*> reify b
  reify (RTForall (Ground bnd)) = TyForall <$> reify bnd
  reify _ = Nothing

  quote RTUnit = ("Unit", [])
  quote RTInt = ("Int", [])
  quote (RTVar a) = ("Var", [Field a])
  quote (RTArr a b) = ("Arr", [Field a, Field b])
  quote (RTForall bnd) = ("Forall", [Field bnd])

  mapReified _ RTUnit = RTUnit
  mapReified _ RTInt = RTInt
  mapReified f (RTVar a) = RTVar (f a)
  mapReified f (RTArr a b) = RTArr (f a) (f b)
  mapReified f (RTForall bnd) = RTForall (f bnd)

instance Repr Tm where
  data Reified Tm
    = RVar (Logic Nom)
    | RLam (Logic Ty) (Logic (Bind Nom Tm))
    | RApp (Logic Tm) (Logic Tm)
    | RInt (Logic Nat)
    | RTAbs (Logic (Bind TyNom Tm))
    | RTApp (Logic Tm) (Logic Ty)

  project (TmVar x) = RVar (Ground (project x))
  project (TmLam ty bnd) = RLam (Ground (project ty)) (Ground (project bnd))
  project (TmApp t1 t2) = RApp (Ground (project t1)) (Ground (project t2))
  project (TmInt n) = RInt (Ground (project n))
  project (TmTAbs bnd) = RTAbs (Ground (project bnd))
  project (TmTApp t ty) = RTApp (Ground (project t)) (Ground (project ty))

  reify (RVar (Ground x)) = TmVar <$> reify x
  reify (RLam (Ground ty) (Ground bnd)) = TmLam <$> reify ty <*> reify bnd
  reify (RApp (Ground t1) (Ground t2)) = TmApp <$> reify t1 <*> reify t2
  reify (RInt (Ground n)) = TmInt <$> reify n
  reify (RTAbs (Ground bnd)) = TmTAbs <$> reify bnd
  reify (RTApp (Ground t) (Ground ty)) = TmTApp <$> reify t <*> reify ty
  reify _ = Nothing

  quote (RVar x) = ("Var", [Field x])
  quote (RLam ty bnd) = ("Lam", [Field ty, Field bnd])
  quote (RApp t1 t2) = ("App", [Field t1, Field t2])
  quote (RInt n) = ("Int", [Field n])
  quote (RTAbs bnd) = ("TAbs", [Field bnd])
  quote (RTApp t ty) = ("TApp", [Field t, Field ty])

  mapReified f (RVar x) = RVar (f x)
  mapReified f (RLam ty bnd) = RLam (f ty) (f bnd)
  mapReified f (RApp t1 t2) = RApp (f t1) (f t2)
  mapReified f (RInt n) = RInt (f n)
  mapReified f (RTAbs bnd) = RTAbs (f bnd)
  mapReified f (RTApp t ty) = RTApp (f t) (f ty)

instance Repr Ctx where
  data Reified Ctx
    = REmpty
    | RVarCtx (Logic Nom) (Logic Ty) (Logic Ctx)
    | RTyCtx (Logic TyNom) (Logic Ctx)

  project CEmpty = REmpty
  project (CVar x ty ctx) = RVarCtx (Ground (project x)) (Ground (project ty)) (Ground (project ctx))
  project (CTy a ctx) = RTyCtx (Ground (project a)) (Ground (project ctx))

  reify REmpty = Just CEmpty
  reify (RVarCtx (Ground x) (Ground ty) (Ground ctx)) = CVar <$> reify x <*> reify ty <*> reify ctx
  reify (RTyCtx (Ground a) (Ground ctx)) = CTy <$> reify a <*> reify ctx
  reify _ = Nothing

  quote REmpty = ("Empty", [])
  quote (RVarCtx x ty ctx) = ("CVar", [Field x, Field ty, Field ctx])
  quote (RTyCtx a ctx) = ("CTy", [Field a, Field ctx])

  mapReified _ REmpty = REmpty
  mapReified f (RVarCtx x ty ctx) = RVarCtx (f x) (f ty) (f ctx)
  mapReified f (RTyCtx a ctx) = RTyCtx (f a) (f ctx)

--------------------------------------------------------------------------------
-- Pretty instances
--------------------------------------------------------------------------------

instance Pretty Ty where
  varNames = cycleNames ["A", "B", "C", "D"]
  prettyReified RTUnit = pure "Unit"
  prettyReified RTInt = pure "Int"
  prettyReified (RTVar a) = prettyLogic a
  prettyReified (RTArr a b) = do
    da <- prettyLogic a
    db <- prettyLogic b
    pure (parens (da <+> " -> " <+> db))
  prettyReified (RTForall bnd) =
    prettyForall bnd

instance Pretty Tm where
  varNames = cycleNames ["e"]
  prettyReified (RVar x) = prettyLogic x
  prettyReified (RInt n) = prettyLogic n
  prettyReified (RApp t1 t2) = do
    d1 <- prettyLogic t1
    d2 <- prettyLogic t2
    pure (parens (d1 <+> " " <+> d2))
  prettyReified (RLam ty bnd) = do
    dty <- prettyLogic ty
    (dn, db) <- prettyBind bnd
    pure (Doc "\\" <+> dn <+> Doc ":" <+> dty <+> Doc ". " <+> db)
  prettyReified (RTAbs bnd) = do
    (dn, db) <- prettyBind bnd
    pure (Doc "/\\" <+> dn <+> Doc ". " <+> db)
  prettyReified (RTApp t ty) = do
    dt <- prettyLogic t
    dty <- prettyLogic ty
    pure (dt <+> Doc " @" <+> dty)

instance Pretty Ctx where
  varNames = cycleNames ["\\u0393"]
  prettyReified REmpty = pure "."
  prettyReified (RVarCtx x ty ctx) = do
    dx <- prettyLogic x
    dty <- prettyLogic ty
    dctx <- prettyLogic ctx
    pure (dctx <+> Doc ", " <+> dx <+> Doc ":" <+> dty)
  prettyReified (RTyCtx a ctx) = do
    da <- prettyLogic a
    dctx <- prettyLogic ctx
    pure (dctx <+> Doc ", " <+> da)

prettyBind
  :: forall name body.
     (NominalAtom name, Permute name body, Pretty name, Pretty body)
  => Logic (Bind name body)
  -> PrettyM (Doc, Doc)
prettyBind bnd =
  case unbind bnd of
    Just (n, body) -> do
      dn <- prettyLogic n
      db <- prettyLogic body
      pure (dn, db)
    Nothing -> do
      d <- prettyLogic bnd
      pure (d, d)

prettyForall
  :: Logic (Bind TyNom Ty)
  -> PrettyM Doc
prettyForall bnd =
  do
    (dn, db) <- prettyBind bnd
    pure (Doc "forall " <+> dn <+> Doc ". " <+> db)

--------------------------------------------------------------------------------
-- Permute/Hash instances
--------------------------------------------------------------------------------

instance Permute TyNom Ty where
  swap a b ty =
    case ty of
      TyUnit -> TyUnit
      TyInt -> TyInt
      TyVar x -> TyVar (swap a b x)
      TyArr t1 t2 -> TyArr (swap a b t1) (swap a b t2)
      TyForall bnd -> TyForall (swap a b bnd)

instance Permute TyNom Tm where
  swap a b tm =
    case tm of
      TmVar x -> TmVar x
      TmLam ty bnd -> TmLam (swap a b ty) (swap a b bnd)
      TmApp t1 t2 -> TmApp (swap a b t1) (swap a b t2)
      TmInt n -> TmInt n
      TmTAbs bnd -> TmTAbs (swap a b bnd)
      TmTApp t ty -> TmTApp (swap a b t) (swap a b ty)

instance Permute Nom Tm where
  swap a b tm =
    case tm of
      TmVar x -> TmVar (swap a b x)
      TmLam ty bnd -> TmLam ty (swap a b bnd)
      TmApp t1 t2 -> TmApp (swap a b t1) (swap a b t2)
      TmInt n -> TmInt n
      TmTAbs bnd -> TmTAbs bnd
      TmTApp t ty -> TmTApp (swap a b t) ty

instance Hash TyNom Ty where
  occursIn a ty =
    case ty of
      TyUnit -> False
      TyInt -> False
      TyVar b -> a == b
      TyArr t1 t2 -> occursIn a t1 || occursIn a t2
      TyForall (Bind b body) ->
        if a == b
          then False
          else occursIn a body

instance Hash TyNom Tm where
  occursIn a tm =
    case tm of
      TmVar _ -> False
      TmLam ty (Bind _ body) -> occursIn a ty || occursIn a body
      TmApp t1 t2 -> occursIn a t1 || occursIn a t2
      TmInt _ -> False
      TmTAbs (Bind b body) ->
        if a == b
          then False
          else occursIn a body
      TmTApp t ty -> occursIn a t || occursIn a ty

--------------------------------------------------------------------------------
-- Smart constructors
--------------------------------------------------------------------------------

tunit :: Term Ty
tunit = ground TyUnit

tint :: Term Ty
tint = ground TyInt

tvar :: Term TyNom -> Term Ty
tvar = lift1 (\a -> Ground (RTVar a))

tarr :: Term Ty -> Term Ty -> Term Ty
tarr = lift2 (\a b -> Ground (RTArr a b))

tforall :: Term TyNom -> Term Ty -> Term Ty
tforall a body =
  lift1 (\bnd -> Ground (RTForall bnd)) (bind a body)

var :: Term Nom -> Term Tm
var = lift1 (\x -> Ground (RVar x))

lam :: Term Ty -> Term Nom -> Term Tm -> Term Tm
lam ty x body =
  lift2 (\t bnd -> Ground (RLam t bnd)) ty (bind x body)

app :: Term Tm -> Term Tm -> Term Tm
app = lift2 (\t1 t2 -> Ground (RApp t1 t2))

intLit :: Term Nat -> Term Tm
intLit = lift1 (\n -> Ground (RInt n))

tlam :: Term TyNom -> Term Tm -> Term Tm
tlam a body =
  lift1 (\bnd -> Ground (RTAbs bnd)) (bind a body)

tapp :: Term Tm -> Term Ty -> Term Tm
tapp = lift2 (\tm ty -> Ground (RTApp tm ty))

ctxEmpty :: Term Ctx
ctxEmpty = ground CEmpty

ctxVar :: Term Nom -> Term Ty -> Term Ctx -> Term Ctx
ctxVar = lift3 (\x ty ctx -> Ground (RVarCtx x ty ctx))

ctxTy :: Term TyNom -> Term Ctx -> Term Ctx
ctxTy = lift2 (\a ctx -> Ground (RTyCtx a ctx))
