{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module LCTI.Syntax
  ( Ty(..)
  , Tm(..)
  , Polar(..)
  , Env(..)
  , Context(..)
  , tint
  , tbool
  , tvar
  , tarr
  , tforall
  , tuncurry
  , tlist
  , tprod
  , tst
  , litInt
  , litBool
  , var
  , abs
  , absAnn
  , absUncurry
  , absUncurryAnn
  , app
  , appUncurry
  , ann
  , tabs
  , tapp
  , nil
  , pair
  , fst
  , snd
  , pos
  , neg
  , eempty
  , etrm
  , euvar
  , eevar
  , esvar
  , cempty
  , cfulltype
  , cterm
  , cuncurry
  , cfst
  , csnd
  , lnil
  , lcons
  , tup
  ) where

import TypedRedex.Core.Term hiding (var, Var)
import Prelude hiding (abs, fst, snd)
import TypedRedex.Nominal (NominalAtom, Permute(..), Hash(..))
import TypedRedex.Nominal.Bind (Bind(..), bind, unbind)
import TypedRedex.Nominal.Prelude (Nom, TyNom)
import TypedRedex.Pretty
  ( Pretty(..)
  , PrettyM
  , Doc(..)
  , (<+>)
  , parens
  , brackets
  , braces
  , commaSep
  , prettyLogic
  , cycleNames
  )

--------------------------------------------------------------------------------
-- Support instances
--------------------------------------------------------------------------------

instance Repr Int where
  data Reified Int = RInt Int

  project n = RInt n
  reify (RInt n) = Just n
  quote (RInt n) = (show n, [])
  mapReified _ (RInt n) = RInt n

instance Pretty Int where
  varNames = cycleNames ["n", "m", "k"]
  prettyReified (RInt n) = pure (Doc (show n))

instance Repr Bool where
  data Reified Bool = RTrue | RFalse

  project True = RTrue
  project False = RFalse
  reify RTrue = Just True
  reify RFalse = Just False
  quote RTrue = ("true", [])
  quote RFalse = ("false", [])
  mapReified _ RTrue = RTrue
  mapReified _ RFalse = RFalse

instance Pretty Bool where
  varNames = cycleNames ["b"]
  prettyReified RTrue = pure "true"
  prettyReified RFalse = pure "false"

instance (Repr a, Repr b) => Repr (a, b) where
  data Reified (a, b) = RTuple (Logic a) (Logic b)

  project (a, b) = RTuple (Ground (project a)) (Ground (project b))
  reify (RTuple (Ground a) (Ground b)) = (,) <$> reify a <*> reify b
  reify _ = Nothing
  quote (RTuple a b) = ("Pair", [Field a, Field b])
  mapReified f (RTuple a b) = RTuple (f a) (f b)

instance (Pretty a, Pretty b) => Pretty (a, b) where
  varNames = cycleNames ["p"]
  prettyReified (RTuple a b) = do
    da <- prettyLogic a
    db <- prettyLogic b
    pure (parens (da <+> Doc ", " <+> db))

instance Repr a => Repr [a] where
  data Reified [a] = RListNil | RListCons (Logic a) (Logic [a])

  project [] = RListNil
  project (x:xs) = RListCons (Ground (project x)) (Ground (project xs))

  reify RListNil = Just []
  reify (RListCons (Ground x) (Ground xs)) = (:) <$> reify x <*> reify xs
  reify _ = Nothing

  quote RListNil = ("Nil", [])
  quote (RListCons x xs) = ("Cons", [Field x, Field xs])

  mapReified _ RListNil = RListNil
  mapReified f (RListCons x xs) = RListCons (f x) (f xs)

instance Pretty a => Pretty [a] where
  varNames = cycleNames ["xs", "ys"]
  prettyReified r =
    case r of
      RListNil -> pure (brackets mempty)
      RListCons x xs -> do
        dx <- prettyLogic x
        rest <- collectListDocs xs
        case rest of
          Just ds -> pure (brackets (commaSep (dx : ds)))
          Nothing -> do
            dxs <- prettyLogic xs
            pure (dx <+> Doc " : " <+> dxs)

collectListDocs :: Pretty a => Logic [a] -> PrettyM (Maybe [Doc])
collectListDocs (Ground RListNil) = pure (Just [])
collectListDocs (Ground (RListCons x xs)) = do
  dx <- prettyLogic x
  rest <- collectListDocs xs
  pure (fmap (dx :) rest)
collectListDocs _ = pure Nothing

prettyListWith :: Pretty a => (Doc -> Doc) -> Logic [a] -> PrettyM Doc
prettyListWith wrap list = do
  items <- collectListDocs list
  case items of
    Just ds -> pure (wrap (commaSep ds))
    Nothing -> prettyLogic list

--------------------------------------------------------------------------------
-- Syntax
--------------------------------------------------------------------------------

data Ty
  = TInt
  | TBool
  | TVar TyNom
  | TArr Ty Ty
  | TForall (Bind TyNom Ty)
  | TUncurry [Ty] Ty
  | TList Ty
  | TProd Ty Ty
  | TST Ty Ty
  deriving (Eq, Show)

data Tm
  = LitInt Int
  | LitBool Bool
  | Var Nom
  | Abs (Bind Nom Tm)
  | AbsAnn (Bind (Nom, Ty) Tm)
  | AbsUncurry (Bind [Nom] Tm)
  | AbsUncurryAnn (Bind [(Nom, Ty)] Tm)
  | App Tm Tm
  | AppUncurry Tm [Tm]
  | Ann Tm Ty
  | TAbs (Bind TyNom Tm)
  | TApp Tm Ty
  | Nil
  | Pair Tm Tm
  | Fst Tm
  | Snd Tm
  deriving (Eq, Show)

data Polar = Pos | Neg
  deriving (Eq, Show)

data Env
  = EEmpty
  | ETrm Nom Ty Env
  | EUvar TyNom Env
  | EEvar TyNom Env
  | ESvar TyNom Ty Env
  deriving (Eq, Show)

data Context
  = CEmpty
  | CFullType Ty
  | CTerm Tm Context
  | CUncurry [Tm] Context
  | CFst Context
  | CSnd Context
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Repr instances
--------------------------------------------------------------------------------

instance Repr Ty where
  data Reified Ty
    = RTInt
    | RTBool
    | RTVar (Logic TyNom)
    | RTArr (Logic Ty) (Logic Ty)
    | RTForall (Logic (Bind TyNom Ty))
    | RTUncurry (Logic [Ty]) (Logic Ty)
    | RTList (Logic Ty)
    | RTProd (Logic Ty) (Logic Ty)
    | RTST (Logic Ty) (Logic Ty)

  project TInt = RTInt
  project TBool = RTBool
  project (TVar a) = RTVar (Ground (project a))
  project (TArr a b) = RTArr (Ground (project a)) (Ground (project b))
  project (TForall bnd) = RTForall (Ground (project bnd))
  project (TUncurry tys ty) = RTUncurry (Ground (project tys)) (Ground (project ty))
  project (TList ty) = RTList (Ground (project ty))
  project (TProd a b) = RTProd (Ground (project a)) (Ground (project b))
  project (TST a b) = RTST (Ground (project a)) (Ground (project b))

  reify RTInt = Just TInt
  reify RTBool = Just TBool
  reify (RTVar (Ground a)) = TVar <$> reify a
  reify (RTArr (Ground a) (Ground b)) = TArr <$> reify a <*> reify b
  reify (RTForall (Ground bnd)) = TForall <$> reify bnd
  reify (RTUncurry (Ground tys) (Ground ty)) = TUncurry <$> reify tys <*> reify ty
  reify (RTList (Ground ty)) = TList <$> reify ty
  reify (RTProd (Ground a) (Ground b)) = TProd <$> reify a <*> reify b
  reify (RTST (Ground a) (Ground b)) = TST <$> reify a <*> reify b
  reify _ = Nothing

  quote RTInt = ("Int", [])
  quote RTBool = ("Bool", [])
  quote (RTVar a) = ("Var", [Field a])
  quote (RTArr a b) = ("Arr", [Field a, Field b])
  quote (RTForall bnd) = ("Forall", [Field bnd])
  quote (RTUncurry tys ty) = ("Uncurry", [Field tys, Field ty])
  quote (RTList ty) = ("List", [Field ty])
  quote (RTProd a b) = ("Prod", [Field a, Field b])
  quote (RTST a b) = ("ST", [Field a, Field b])

  mapReified _ RTInt = RTInt
  mapReified _ RTBool = RTBool
  mapReified f (RTVar a) = RTVar (f a)
  mapReified f (RTArr a b) = RTArr (f a) (f b)
  mapReified f (RTForall bnd) = RTForall (f bnd)
  mapReified f (RTUncurry tys ty) = RTUncurry (f tys) (f ty)
  mapReified f (RTList ty) = RTList (f ty)
  mapReified f (RTProd a b) = RTProd (f a) (f b)
  mapReified f (RTST a b) = RTST (f a) (f b)

instance Repr Tm where
  data Reified Tm
    = RLitInt (Logic Int)
    | RLitBool (Logic Bool)
    | RVar (Logic Nom)
    | RAbs (Logic (Bind Nom Tm))
    | RAbsAnn (Logic (Bind (Nom, Ty) Tm))
    | RAbsUncurry (Logic (Bind [Nom] Tm))
    | RAbsUncurryAnn (Logic (Bind [(Nom, Ty)] Tm))
    | RApp (Logic Tm) (Logic Tm)
    | RAppUncurry (Logic Tm) (Logic [Tm])
    | RAnn (Logic Tm) (Logic Ty)
    | RTAbs (Logic (Bind TyNom Tm))
    | RTApp (Logic Tm) (Logic Ty)
    | RNil
    | RPair (Logic Tm) (Logic Tm)
    | RFst (Logic Tm)
    | RSnd (Logic Tm)

  project (LitInt n) = RLitInt (Ground (project n))
  project (LitBool b) = RLitBool (Ground (project b))
  project (Var x) = RVar (Ground (project x))
  project (Abs bnd) = RAbs (Ground (project bnd))
  project (AbsAnn bnd) = RAbsAnn (Ground (project bnd))
  project (AbsUncurry bnd) = RAbsUncurry (Ground (project bnd))
  project (AbsUncurryAnn bnd) = RAbsUncurryAnn (Ground (project bnd))
  project (App t1 t2) = RApp (Ground (project t1)) (Ground (project t2))
  project (AppUncurry t ts) = RAppUncurry (Ground (project t)) (Ground (project ts))
  project (Ann t ty) = RAnn (Ground (project t)) (Ground (project ty))
  project (TAbs bnd) = RTAbs (Ground (project bnd))
  project (TApp t ty) = RTApp (Ground (project t)) (Ground (project ty))
  project Nil = RNil
  project (Pair t1 t2) = RPair (Ground (project t1)) (Ground (project t2))
  project (Fst t) = RFst (Ground (project t))
  project (Snd t) = RSnd (Ground (project t))

  reify (RLitInt (Ground n)) = LitInt <$> reify n
  reify (RLitBool (Ground b)) = LitBool <$> reify b
  reify (RVar (Ground x)) = Var <$> reify x
  reify (RAbs (Ground bnd)) = Abs <$> reify bnd
  reify (RAbsAnn (Ground bnd)) = AbsAnn <$> reify bnd
  reify (RAbsUncurry (Ground bnd)) = AbsUncurry <$> reify bnd
  reify (RAbsUncurryAnn (Ground bnd)) = AbsUncurryAnn <$> reify bnd
  reify (RApp (Ground t1) (Ground t2)) = App <$> reify t1 <*> reify t2
  reify (RAppUncurry (Ground t) (Ground ts)) = AppUncurry <$> reify t <*> reify ts
  reify (RAnn (Ground t) (Ground ty)) = Ann <$> reify t <*> reify ty
  reify (RTAbs (Ground bnd)) = TAbs <$> reify bnd
  reify (RTApp (Ground t) (Ground ty)) = TApp <$> reify t <*> reify ty
  reify RNil = Just Nil
  reify (RPair (Ground t1) (Ground t2)) = Pair <$> reify t1 <*> reify t2
  reify (RFst (Ground t)) = Fst <$> reify t
  reify (RSnd (Ground t)) = Snd <$> reify t
  reify _ = Nothing

  quote (RLitInt n) = ("LitInt", [Field n])
  quote (RLitBool b) = ("LitBool", [Field b])
  quote (RVar x) = ("Var", [Field x])
  quote (RAbs bnd) = ("Abs", [Field bnd])
  quote (RAbsAnn bnd) = ("AbsAnn", [Field bnd])
  quote (RAbsUncurry bnd) = ("AbsUncurry", [Field bnd])
  quote (RAbsUncurryAnn bnd) = ("AbsUncurryAnn", [Field bnd])
  quote (RApp t1 t2) = ("App", [Field t1, Field t2])
  quote (RAppUncurry t ts) = ("AppUncurry", [Field t, Field ts])
  quote (RAnn t ty) = ("Ann", [Field t, Field ty])
  quote (RTAbs bnd) = ("TAbs", [Field bnd])
  quote (RTApp t ty) = ("TApp", [Field t, Field ty])
  quote RNil = ("Nil", [])
  quote (RPair t1 t2) = ("Pair", [Field t1, Field t2])
  quote (RFst t) = ("Fst", [Field t])
  quote (RSnd t) = ("Snd", [Field t])

  mapReified f (RLitInt n) = RLitInt (f n)
  mapReified f (RLitBool b) = RLitBool (f b)
  mapReified f (RVar x) = RVar (f x)
  mapReified f (RAbs bnd) = RAbs (f bnd)
  mapReified f (RAbsAnn bnd) = RAbsAnn (f bnd)
  mapReified f (RAbsUncurry bnd) = RAbsUncurry (f bnd)
  mapReified f (RAbsUncurryAnn bnd) = RAbsUncurryAnn (f bnd)
  mapReified f (RApp t1 t2) = RApp (f t1) (f t2)
  mapReified f (RAppUncurry t ts) = RAppUncurry (f t) (f ts)
  mapReified f (RAnn t ty) = RAnn (f t) (f ty)
  mapReified f (RTAbs bnd) = RTAbs (f bnd)
  mapReified f (RTApp t ty) = RTApp (f t) (f ty)
  mapReified _ RNil = RNil
  mapReified f (RPair t1 t2) = RPair (f t1) (f t2)
  mapReified f (RFst t) = RFst (f t)
  mapReified f (RSnd t) = RSnd (f t)

instance Repr Polar where
  data Reified Polar = RPos | RNeg

  project Pos = RPos
  project Neg = RNeg

  reify RPos = Just Pos
  reify RNeg = Just Neg

  quote RPos = ("Pos", [])
  quote RNeg = ("Neg", [])

  mapReified _ RPos = RPos
  mapReified _ RNeg = RNeg

instance Repr Env where
  data Reified Env
    = REmpty
    | RTrm (Logic Nom) (Logic Ty) (Logic Env)
    | RUvar (Logic TyNom) (Logic Env)
    | REvar (Logic TyNom) (Logic Env)
    | RSvar (Logic TyNom) (Logic Ty) (Logic Env)

  project EEmpty = REmpty
  project (ETrm x ty env) = RTrm (Ground (project x)) (Ground (project ty)) (Ground (project env))
  project (EUvar a env) = RUvar (Ground (project a)) (Ground (project env))
  project (EEvar a env) = REvar (Ground (project a)) (Ground (project env))
  project (ESvar a ty env) = RSvar (Ground (project a)) (Ground (project ty)) (Ground (project env))

  reify REmpty = Just EEmpty
  reify (RTrm (Ground x) (Ground ty) (Ground env)) = ETrm <$> reify x <*> reify ty <*> reify env
  reify (RUvar (Ground a) (Ground env)) = EUvar <$> reify a <*> reify env
  reify (REvar (Ground a) (Ground env)) = EEvar <$> reify a <*> reify env
  reify (RSvar (Ground a) (Ground ty) (Ground env)) = ESvar <$> reify a <*> reify ty <*> reify env
  reify _ = Nothing

  quote REmpty = ("Empty", [])
  quote (RTrm x ty env) = ("ETrm", [Field x, Field ty, Field env])
  quote (RUvar a env) = ("EUvar", [Field a, Field env])
  quote (REvar a env) = ("EEvar", [Field a, Field env])
  quote (RSvar a ty env) = ("ESvar", [Field a, Field ty, Field env])

  mapReified _ REmpty = REmpty
  mapReified f (RTrm x ty env) = RTrm (f x) (f ty) (f env)
  mapReified f (RUvar a env) = RUvar (f a) (f env)
  mapReified f (REvar a env) = REvar (f a) (f env)
  mapReified f (RSvar a ty env) = RSvar (f a) (f ty) (f env)

instance Repr Context where
  data Reified Context
    = RCEmpty
    | RCFullType (Logic Ty)
    | RCTerm (Logic Tm) (Logic Context)
    | RCUncurry (Logic [Tm]) (Logic Context)
    | RCFst (Logic Context)
    | RCSnd (Logic Context)

  project CEmpty = RCEmpty
  project (CFullType ty) = RCFullType (Ground (project ty))
  project (CTerm tm ctx) = RCTerm (Ground (project tm)) (Ground (project ctx))
  project (CUncurry tms ctx) = RCUncurry (Ground (project tms)) (Ground (project ctx))
  project (CFst ctx) = RCFst (Ground (project ctx))
  project (CSnd ctx) = RCSnd (Ground (project ctx))

  reify RCEmpty = Just CEmpty
  reify (RCFullType (Ground ty)) = CFullType <$> reify ty
  reify (RCTerm (Ground tm) (Ground ctx)) = CTerm <$> reify tm <*> reify ctx
  reify (RCUncurry (Ground tms) (Ground ctx)) = CUncurry <$> reify tms <*> reify ctx
  reify (RCFst (Ground ctx)) = CFst <$> reify ctx
  reify (RCSnd (Ground ctx)) = CSnd <$> reify ctx
  reify _ = Nothing

  quote RCEmpty = ("CEmpty", [])
  quote (RCFullType ty) = ("CFullType", [Field ty])
  quote (RCTerm tm ctx) = ("CTerm", [Field tm, Field ctx])
  quote (RCUncurry tms ctx) = ("CUncurry", [Field tms, Field ctx])
  quote (RCFst ctx) = ("CFst", [Field ctx])
  quote (RCSnd ctx) = ("CSnd", [Field ctx])

  mapReified _ RCEmpty = RCEmpty
  mapReified f (RCFullType ty) = RCFullType (f ty)
  mapReified f (RCTerm tm ctx) = RCTerm (f tm) (f ctx)
  mapReified f (RCUncurry tms ctx) = RCUncurry (f tms) (f ctx)
  mapReified f (RCFst ctx) = RCFst (f ctx)
  mapReified f (RCSnd ctx) = RCSnd (f ctx)

--------------------------------------------------------------------------------
-- Pretty instances
--------------------------------------------------------------------------------

instance Pretty Ty where
  varNames = cycleNames ["A", "B", "C", "D"]
  prettyReified RTInt = pure "int"
  prettyReified RTBool = pure "bool"
  prettyReified (RTVar a) = prettyLogic a
  prettyReified (RTArr a b) = do
    da <- prettyLogic a
    db <- prettyLogic b
    pure (parens (da <+> Doc " -> " <+> db))
  prettyReified (RTForall bnd) = prettyForall bnd
  prettyReified (RTUncurry tys ty) = do
    dtys <- prettyListWith braces tys
    dty <- prettyLogic ty
    pure (dtys <+> Doc " -> " <+> dty)
  prettyReified (RTList ty) = do
    dty <- prettyLogic ty
    pure (brackets dty)
  prettyReified (RTProd a b) = do
    da <- prettyLogic a
    db <- prettyLogic b
    pure (parens (da <+> Doc " * " <+> db))
  prettyReified (RTST a b) = do
    da <- prettyLogic a
    db <- prettyLogic b
    pure (Doc "ST " <+> da <+> Doc " " <+> db)

instance Pretty Tm where
  varNames = cycleNames ["e"]
  prettyReified (RLitInt n) = prettyLogic n
  prettyReified (RLitBool b) = prettyLogic b
  prettyReified (RVar x) = prettyLogic x
  prettyReified (RAbs bnd) = do
    (dn, db) <- prettyBind bnd
    pure (Doc "\\" <+> dn <+> Doc ". " <+> db)
  prettyReified (RAbsAnn bnd) = do
    (dn, dty, db) <- prettyBindAnn bnd
    pure (Doc "\\" <+> dn <+> Doc " : " <+> dty <+> Doc ". " <+> db)
  prettyReified (RAbsUncurry bnd) = do
    (dns, db) <- prettyBindList bnd
    pure (Doc "\\" <+> dns <+> Doc ". " <+> db)
  prettyReified (RAbsUncurryAnn bnd) = do
    (dns, db) <- prettyBindAnnList bnd
    pure (Doc "\\" <+> dns <+> Doc ". " <+> db)
  prettyReified (RApp t1 t2) = do
    d1 <- prettyLogic t1
    d2 <- prettyLogic t2
    pure (parens (d1 <+> Doc " " <+> d2))
  prettyReified (RAppUncurry t ts) = do
    d1 <- prettyLogic t
    dts <- prettyListWith braces ts
    pure (d1 <+> Doc " " <+> dts)
  prettyReified (RAnn t ty) = do
    dt <- prettyLogic t
    dty <- prettyLogic ty
    pure (parens (dt <+> Doc " : " <+> dty))
  prettyReified (RTAbs bnd) = do
    (dn, db) <- prettyBind bnd
    pure (Doc "/\\" <+> dn <+> Doc ". " <+> db)
  prettyReified (RTApp t ty) = do
    dt <- prettyLogic t
    dty <- prettyLogic ty
    pure (dt <+> Doc " @ " <+> dty)
  prettyReified RNil = pure "nil"
  prettyReified (RPair t1 t2) = do
    d1 <- prettyLogic t1
    d2 <- prettyLogic t2
    pure (Doc "<" <+> d1 <+> Doc ", " <+> d2 <+> Doc ">")
  prettyReified (RFst t) = do
    dt <- prettyLogic t
    pure (Doc "fst " <+> dt)
  prettyReified (RSnd t) = do
    dt <- prettyLogic t
    pure (Doc "snd " <+> dt)

instance Pretty Polar where
  varNames = cycleNames ["p"]
  prettyReified RPos = pure "<=+"
  prettyReified RNeg = pure "<=-"

instance Pretty Env where
  varNames = cycleNames ["G"]
  prettyReified REmpty = pure "."
  prettyReified (RTrm x ty env) = do
    dx <- prettyLogic x
    dty <- prettyLogic ty
    denv <- prettyLogic env
    pure (denv <+> Doc ", " <+> dx <+> Doc ":" <+> dty)
  prettyReified (RUvar a env) = do
    da <- prettyLogic a
    denv <- prettyLogic env
    pure (denv <+> Doc ", " <+> da)
  prettyReified (REvar a env) = do
    da <- prettyLogic a
    denv <- prettyLogic env
    pure (denv <+> Doc ", " <+> da <+> Doc "^")
  prettyReified (RSvar a ty env) = do
    da <- prettyLogic a
    dty <- prettyLogic ty
    denv <- prettyLogic env
    pure (denv <+> Doc ", " <+> da <+> Doc "=" <+> dty)

instance Pretty Context where
  varNames = cycleNames ["S"]
  prettyReified RCEmpty = pure "[]"
  prettyReified (RCFullType ty) = prettyLogic ty
  prettyReified (RCTerm tm ctx) = do
    dtm <- prettyLogic tm
    dctx <- prettyLogic ctx
    pure (brackets dtm <+> Doc " ~> " <+> dctx)
  prettyReified (RCUncurry tms ctx) = do
    dtms <- prettyListWith braces tms
    dctx <- prettyLogic ctx
    pure (dtms <+> Doc " ~> " <+> dctx)
  prettyReified (RCFst ctx) = do
    dctx <- prettyLogic ctx
    pure (Doc "fst ~> " <+> dctx)
  prettyReified (RCSnd ctx) = do
    dctx <- prettyLogic ctx
    pure (Doc "snd ~> " <+> dctx)

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

prettyBindList
  :: forall name body.
     (NominalAtom [name], Permute [name] body, Pretty name, Pretty body)
  => Logic (Bind [name] body)
  -> PrettyM (Doc, Doc)
prettyBindList bnd =
  case unbind bnd of
    Just (ns, body) -> do
      dns <- prettyListWith braces ns
      db <- prettyLogic body
      pure (dns, db)
    Nothing -> do
      d <- prettyLogic bnd
      pure (d, d)

prettyBindAnn
  :: Logic (Bind (Nom, Ty) Tm)
  -> PrettyM (Doc, Doc, Doc)
prettyBindAnn bnd =
  case unbind bnd of
    Just (pair, body) -> do
      (dn, dty) <- prettyAnnPair pair
      db <- prettyLogic body
      pure (dn, dty, db)
    Nothing -> do
      d <- prettyLogic bnd
      pure (d, d, d)

prettyBindAnnList
  :: Logic (Bind [(Nom, Ty)] Tm)
  -> PrettyM (Doc, Doc)
prettyBindAnnList bnd =
  case unbind bnd of
    Just (ns, body) -> do
      dns <- prettyAnnList ns
      db <- prettyLogic body
      pure (dns, db)
    Nothing -> do
      d <- prettyLogic bnd
      pure (d, d)

prettyAnnPair :: Logic (Nom, Ty) -> PrettyM (Doc, Doc)
prettyAnnPair pair =
  case pair of
    Ground (RTuple n ty) -> do
      dn <- prettyLogic n
      dty <- prettyLogic ty
      pure (dn, dty)
    _ -> do
      d <- prettyLogic pair
      pure (d, d)

prettyAnnList :: Logic [(Nom, Ty)] -> PrettyM Doc
prettyAnnList list = do
  items <- collectAnnDocs list
  case items of
    Just ds -> pure (braces (commaSep ds))
    Nothing -> prettyLogic list
  where
    collectAnnDocs (Ground RListNil) = pure (Just [])
    collectAnnDocs (Ground (RListCons x xs)) = do
      (dn, dty) <- prettyAnnPair x
      rest <- collectAnnDocs xs
      pure (fmap ((dn <+> Doc " : " <+> dty) :) rest)
    collectAnnDocs _ = pure Nothing

prettyForall :: Logic (Bind TyNom Ty) -> PrettyM Doc
prettyForall bnd = do
  (dn, db) <- prettyBind bnd
  pure (Doc "forall " <+> dn <+> Doc ". " <+> db)

--------------------------------------------------------------------------------
-- Permute/Hash instances
--------------------------------------------------------------------------------

instance NominalAtom (Nom, Ty)
instance NominalAtom [Nom]
instance NominalAtom [(Nom, Ty)]

instance (Permute name a, Permute name b) => Permute name (a, b) where
  swap a b (x, y) = (swap a b x, swap a b y)

instance Permute name a => Permute name [a] where
  swap a b = map (swap a b)

instance Permute Nom Ty where
  swap _ _ ty = ty

instance Permute TyNom Ty where
  swap a b ty =
    case ty of
      TInt -> TInt
      TBool -> TBool
      TVar x -> TVar (swap a b x)
      TArr t1 t2 -> TArr (swap a b t1) (swap a b t2)
      TForall bnd -> TForall (swap a b bnd)
      TUncurry tys t -> TUncurry (swap a b tys) (swap a b t)
      TList t -> TList (swap a b t)
      TProd t1 t2 -> TProd (swap a b t1) (swap a b t2)
      TST t1 t2 -> TST (swap a b t1) (swap a b t2)

instance Permute TyNom Tm where
  swap a b tm =
    case tm of
      LitInt n -> LitInt n
      LitBool c -> LitBool c
      Var x -> Var x
      Abs bnd -> Abs (swap a b bnd)
      AbsAnn bnd -> AbsAnn (swap a b bnd)
      AbsUncurry bnd -> AbsUncurry (swap a b bnd)
      AbsUncurryAnn bnd -> AbsUncurryAnn (swap a b bnd)
      App t1 t2 -> App (swap a b t1) (swap a b t2)
      AppUncurry t ts -> AppUncurry (swap a b t) (swap a b ts)
      Ann t ty -> Ann (swap a b t) (swap a b ty)
      TAbs bnd -> TAbs (swap a b bnd)
      TApp t ty -> TApp (swap a b t) (swap a b ty)
      Nil -> Nil
      Pair t1 t2 -> Pair (swap a b t1) (swap a b t2)
      Fst t -> Fst (swap a b t)
      Snd t -> Snd (swap a b t)

instance Permute Nom Tm where
  swap a b tm =
    case tm of
      LitInt n -> LitInt n
      LitBool c -> LitBool c
      Var x -> Var (swap a b x)
      Abs bnd -> Abs (swap a b bnd)
      AbsAnn (Bind p body) ->
        AbsAnn (Bind (swap a b p) (swap a b body))
      AbsUncurry (Bind ns body) ->
        AbsUncurry (Bind (swap a b ns) (swap a b body))
      AbsUncurryAnn (Bind ns body) ->
        AbsUncurryAnn (Bind (swap a b ns) (swap a b body))
      App t1 t2 -> App (swap a b t1) (swap a b t2)
      AppUncurry t ts -> AppUncurry (swap a b t) (swap a b ts)
      Ann t ty -> Ann (swap a b t) ty
      TAbs bnd -> TAbs (swap a b bnd)
      TApp t ty -> TApp (swap a b t) ty
      Nil -> Nil
      Pair t1 t2 -> Pair (swap a b t1) (swap a b t2)
      Fst t -> Fst (swap a b t)
      Snd t -> Snd (swap a b t)

instance Permute (Nom, Ty) Tm where
  swap (a, _) (b, _) = swap a b

instance Permute [Nom] Tm where
  swap as bs tm = foldl (\acc (a, b) -> swap a b acc) tm (zip as bs)

instance Permute [(Nom, Ty)] Tm where
  swap as bs tm =
    foldl (\acc ((a, _), (b, _)) -> swap a b acc) tm (zip as bs)

instance Hash TyNom Ty where
  occursIn a ty =
    case ty of
      TInt -> False
      TBool -> False
      TVar b -> a == b
      TArr t1 t2 -> occursIn a t1 || occursIn a t2
      TForall (Bind b body) ->
        if a == b
          then False
          else occursIn a body
      TUncurry tys t -> any (occursIn a) tys || occursIn a t
      TList t -> occursIn a t
      TProd t1 t2 -> occursIn a t1 || occursIn a t2
      TST t1 t2 -> occursIn a t1 || occursIn a t2

instance Hash TyNom Tm where
  occursIn a tm =
    case tm of
      LitInt _ -> False
      LitBool _ -> False
      Var _ -> False
      Abs (Bind _ body) -> occursIn a body
      AbsAnn (Bind (_, ty) body) -> occursIn a ty || occursIn a body
      AbsUncurry (Bind _ body) -> occursIn a body
      AbsUncurryAnn (Bind ns body) ->
        any (occursIn a . (\(_, ty) -> ty)) ns || occursIn a body
      App t1 t2 -> occursIn a t1 || occursIn a t2
      AppUncurry t ts -> occursIn a t || any (occursIn a) ts
      Ann t ty -> occursIn a t || occursIn a ty
      TAbs (Bind b body) -> if a == b then False else occursIn a body
      TApp t ty -> occursIn a t || occursIn a ty
      Nil -> False
      Pair t1 t2 -> occursIn a t1 || occursIn a t2
      Fst t -> occursIn a t
      Snd t -> occursIn a t

instance Hash Nom Tm where
  occursIn a tm =
    case tm of
      LitInt _ -> False
      LitBool _ -> False
      Var b -> a == b
      Abs (Bind b body) -> if a == b then False else occursIn a body
      AbsAnn (Bind (b, _) body) -> if a == b then False else occursIn a body
      AbsUncurry (Bind ns body) -> if a `elem` ns then False else occursIn a body
      AbsUncurryAnn (Bind ns body) ->
        if a `elem` map (\(x, _) -> x) ns
          then False
          else occursIn a body
      App t1 t2 -> occursIn a t1 || occursIn a t2
      AppUncurry t ts -> occursIn a t || any (occursIn a) ts
      Ann t _ -> occursIn a t
      TAbs (Bind _ body) -> occursIn a body
      TApp t _ -> occursIn a t
      Nil -> False
      Pair t1 t2 -> occursIn a t1 || occursIn a t2
      Fst t -> occursIn a t
      Snd t -> occursIn a t

--------------------------------------------------------------------------------
-- Smart constructors
--------------------------------------------------------------------------------

tint :: Term Ty
tint = ground TInt

tbool :: Term Ty
tbool = ground TBool

tvar :: Term TyNom -> Term Ty
tvar = lift1 (\a -> Ground (RTVar a))

tarr :: Term Ty -> Term Ty -> Term Ty
tarr = lift2 (\a b -> Ground (RTArr a b))

tforall :: Term TyNom -> Term Ty -> Term Ty
tforall a body =
  lift1 (\bnd -> Ground (RTForall bnd)) (bind a body)

tuncurry :: Term [Ty] -> Term Ty -> Term Ty
tuncurry = lift2 (\tys ty -> Ground (RTUncurry tys ty))

tlist :: Term Ty -> Term Ty
tlist = lift1 (\ty -> Ground (RTList ty))

tprod :: Term Ty -> Term Ty -> Term Ty
tprod = lift2 (\a b -> Ground (RTProd a b))

tst :: Term Ty -> Term Ty -> Term Ty
tst = lift2 (\a b -> Ground (RTST a b))

litInt :: Term Int -> Term Tm
litInt = lift1 (\n -> Ground (RLitInt n))

litBool :: Term Bool -> Term Tm
litBool = lift1 (\b -> Ground (RLitBool b))

var :: Term Nom -> Term Tm
var = lift1 (\x -> Ground (RVar x))

abs :: Term Nom -> Term Tm -> Term Tm
abs x body =
  lift1 (\bnd -> Ground (RAbs bnd)) (bind x body)

absAnn :: Term (Nom, Ty) -> Term Tm -> Term Tm
absAnn p body =
  lift1 (\bnd -> Ground (RAbsAnn bnd)) (bind p body)

absUncurry :: Term [Nom] -> Term Tm -> Term Tm
absUncurry xs body =
  lift1 (\bnd -> Ground (RAbsUncurry bnd)) (bind xs body)

absUncurryAnn :: Term [(Nom, Ty)] -> Term Tm -> Term Tm
absUncurryAnn xs body =
  lift1 (\bnd -> Ground (RAbsUncurryAnn bnd)) (bind xs body)

app :: Term Tm -> Term Tm -> Term Tm
app = lift2 (\t1 t2 -> Ground (RApp t1 t2))

appUncurry :: Term Tm -> Term [Tm] -> Term Tm
appUncurry = lift2 (\t ts -> Ground (RAppUncurry t ts))

ann :: Term Tm -> Term Ty -> Term Tm
ann = lift2 (\t ty -> Ground (RAnn t ty))

tabs :: Term TyNom -> Term Tm -> Term Tm
tabs a body =
  lift1 (\bnd -> Ground (RTAbs bnd)) (bind a body)

tapp :: Term Tm -> Term Ty -> Term Tm
tapp = lift2 (\t ty -> Ground (RTApp t ty))

nil :: Term Tm
nil = ground Nil

pair :: Term Tm -> Term Tm -> Term Tm
pair = lift2 (\t1 t2 -> Ground (RPair t1 t2))

fst :: Term Tm -> Term Tm
fst = lift1 (\t -> Ground (RFst t))

snd :: Term Tm -> Term Tm
snd = lift1 (\t -> Ground (RSnd t))

pos :: Term Polar
pos = ground Pos

neg :: Term Polar
neg = ground Neg

eempty :: Term Env
eempty = ground EEmpty

etrm :: Term Nom -> Term Ty -> Term Env -> Term Env
etrm = lift3 (\x ty env -> Ground (RTrm x ty env))

euvar :: Term TyNom -> Term Env -> Term Env
euvar = lift2 (\a env -> Ground (RUvar a env))

eevar :: Term TyNom -> Term Env -> Term Env
eevar = lift2 (\a env -> Ground (REvar a env))

esvar :: Term TyNom -> Term Ty -> Term Env -> Term Env
esvar = lift3 (\a ty env -> Ground (RSvar a ty env))

cempty :: Term Context
cempty = ground CEmpty

cfulltype :: Term Ty -> Term Context
cfulltype = lift1 (\ty -> Ground (RCFullType ty))

cterm :: Term Tm -> Term Context -> Term Context
cterm = lift2 (\tm ctx -> Ground (RCTerm tm ctx))

cuncurry :: Term [Tm] -> Term Context -> Term Context
cuncurry = lift2 (\tms ctx -> Ground (RCUncurry tms ctx))

cfst :: Term Context -> Term Context
cfst = lift1 (\ctx -> Ground (RCFst ctx))

csnd :: Term Context -> Term Context
csnd = lift1 (\ctx -> Ground (RCSnd ctx))

lnil :: Repr a => Term [a]
lnil = ground []

lcons :: Repr a => Term a -> Term [a] -> Term [a]
lcons = lift2 (\x xs -> Ground (RListCons x xs))

tup :: (Repr a, Repr b) => Term a -> Term b -> Term (a, b)
tup = lift2 (\a b -> Ground (RTuple a b))
