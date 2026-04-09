{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module LTI.Syntax
  ( Ty(..)
  , Tm(..)
  , ttop
  , tbot
  , tvar
  , tarr
  , tforall
  , var
  , lam
  , app
  , lnil
  , lcons
  , tup
  ) where

{-
This module is intended to contain syntax definitions for the LTI system. (Local Type Inference from Pierce and Turner 2000)

the [_] means a list of zero or more elements.

type A := a -- type variable
        | top -- top type
        | bot -- bottom type
        | forall [a]. [A] -> B -- function type with universal quantification

expression := x -- term variable
            | lam[a][x : A]. e
            | e @[A] ([e])


-}

import TypedRedex.Core.Term hiding (var, Var)
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
  , commaSep
  , prettyLogic
  , cycleNames
  )

--------------------------------------------------------------------------------
-- Support instances (lists/tuples)
--------------------------------------------------------------------------------

-- NOTE: These list/tuple instances are defined locally (mirroring LCTI) so we
-- can use lists in the object language syntax and render them nicely.

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
  = TTop
  | TBot
  | TVar TyNom
  | TArr [Ty] Ty
  | TForall (Bind [TyNom] Ty)
  deriving (Eq, Show)

data Tm
  = Var Nom
  -- | @lam[a][x : A]. e@ is represented as a nested binder:
  --   the outer binder binds type variables (scoping over annotations and body),
  --   and the inner binder binds term variables (scoping over the body).
  | Lam (Bind [TyNom] (Bind [(Nom, Ty)] Tm))
  -- | @e @[A] ([e])@: explicit type arguments and term arguments.
  | App Tm [Ty] [Tm]
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Repr instances
--------------------------------------------------------------------------------

instance Repr Ty where
  data Reified Ty
    = RTTop
    | RTBot
    | RTVar (Logic TyNom)
    | RTArr (Logic [Ty]) (Logic Ty)
    | RTForall (Logic (Bind [TyNom] Ty))

  project TTop = RTTop
  project TBot = RTBot
  project (TVar a) = RTVar (Ground (project a))
  project (TArr as b) = RTArr (Ground (project as)) (Ground (project b))
  project (TForall bnd) = RTForall (Ground (project bnd))

  reify RTTop = Just TTop
  reify RTBot = Just TBot
  reify (RTVar (Ground a)) = TVar <$> reify a
  reify (RTArr (Ground as) (Ground b)) = TArr <$> reify as <*> reify b
  reify (RTForall (Ground bnd)) = TForall <$> reify bnd
  reify _ = Nothing

  quote RTTop = ("Top", [])
  quote RTBot = ("Bot", [])
  quote (RTVar a) = ("Var", [Field a])
  quote (RTArr as b) = ("Arr", [Field as, Field b])
  quote (RTForall bnd) = ("Forall", [Field bnd])

  mapReified _ RTTop = RTTop
  mapReified _ RTBot = RTBot
  mapReified f (RTVar a) = RTVar (f a)
  mapReified f (RTArr as b) = RTArr (f as) (f b)
  mapReified f (RTForall bnd) = RTForall (f bnd)

instance Repr Tm where
  data Reified Tm
    = RVar (Logic Nom)
    | RLam (Logic (Bind [TyNom] (Bind [(Nom, Ty)] Tm)))
    | RApp (Logic Tm) (Logic [Ty]) (Logic [Tm])

  project (Var x) = RVar (Ground (project x))
  project (Lam bnd) = RLam (Ground (project bnd))
  project (App t tys ts) =
    RApp (Ground (project t)) (Ground (project tys)) (Ground (project ts))

  reify (RVar (Ground x)) = Var <$> reify x
  reify (RLam (Ground bnd)) = Lam <$> reify bnd
  reify (RApp (Ground t) (Ground tys) (Ground ts)) =
    App <$> reify t <*> reify tys <*> reify ts
  reify _ = Nothing

  quote (RVar x) = ("Var", [Field x])
  quote (RLam bnd) = ("Lam", [Field bnd])
  quote (RApp t tys ts) = ("App", [Field t, Field tys, Field ts])

  mapReified f (RVar x) = RVar (f x)
  mapReified f (RLam bnd) = RLam (f bnd)
  mapReified f (RApp t tys ts) = RApp (f t) (f tys) (f ts)

--------------------------------------------------------------------------------
-- Pretty instances
--------------------------------------------------------------------------------

instance Pretty Ty where
  varNames = cycleNames ["A", "B", "C", "D"]
  prettyReified RTTop = pure "top"
  prettyReified RTBot = pure "bot"
  prettyReified (RTVar a) = prettyLogic a
  prettyReified (RTArr as b) = do
    das <- prettyListWith brackets as
    db <- prettyLogic b
    pure (das <+> Doc " -> " <+> db)
  prettyReified (RTForall bnd) = prettyForall bnd

instance Pretty Tm where
  varNames = cycleNames ["e"]
  prettyReified (RVar x) = prettyLogic x
  prettyReified (RLam bnd) = prettyLam bnd
  prettyReified (RApp t tys ts) = do
    dt <- prettyLogic t
    dtys <- prettyListWith brackets tys
    dts <- prettyListWith parens ts
    pure (dt <+> Doc " @" <+> dtys <+> Doc " " <+> dts)

prettyForall :: Logic (Bind [TyNom] Ty) -> PrettyM Doc
prettyForall bnd =
  case unbind bnd of
    Just (as, body) -> do
      das <- prettyListWith brackets as
      db <- prettyLogic body
      pure (Doc "forall " <+> das <+> Doc ". " <+> db)
    Nothing -> do
      d <- prettyLogic bnd
      pure (Doc "forall " <+> d)

prettyLam :: Logic (Bind [TyNom] (Bind [(Nom, Ty)] Tm)) -> PrettyM Doc
prettyLam bnd =
  case unbind bnd of
    Just (as, inner) ->
      case unbind inner of
        Just (xs, body) -> do
          das <- prettyListWith brackets as
          dxs <- prettyAnnList xs
          db <- prettyLogic body
          pure (Doc "lam" <+> das <+> dxs <+> Doc ". " <+> db)
        Nothing -> do
          d <- prettyLogic inner
          das <- prettyListWith brackets as
          pure (Doc "lam" <+> das <+> Doc "." <+> d)
    Nothing -> prettyLogic bnd

prettyAnnPair :: Logic (Nom, Ty) -> PrettyM Doc
prettyAnnPair pair =
  case pair of
    Ground (RTuple n ty) -> do
      dn <- prettyLogic n
      dty <- prettyLogic ty
      pure (dn <+> Doc " : " <+> dty)
    _ -> prettyLogic pair

prettyAnnList :: Logic [(Nom, Ty)] -> PrettyM Doc
prettyAnnList list = do
  items <- collectAnnDocs list
  case items of
    Just ds -> pure (brackets (commaSep ds))
    Nothing -> prettyLogic list
  where
    collectAnnDocs (Ground RListNil) = pure (Just [])
    collectAnnDocs (Ground (RListCons x xs)) = do
      dx <- prettyAnnPair x
      rest <- collectAnnDocs xs
      pure (fmap (dx :) rest)
    collectAnnDocs _ = pure Nothing

--------------------------------------------------------------------------------
-- Permute/Hash instances
--------------------------------------------------------------------------------

instance NominalAtom [TyNom]
instance NominalAtom (Nom, Ty)
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
      TTop -> TTop
      TBot -> TBot
      TVar x -> TVar (swap a b x)
      TArr as r -> TArr (swap a b as) (swap a b r)
      TForall (Bind as body) ->
        -- Swap inside the bound-name list as well; this keeps the meaning of
        -- the binder stable under permutation.
        TForall (Bind (swap a b as) (swap a b body))

-- Swapping a vector of type variables performs elementwise swaps (by position).
instance Permute [TyNom] Ty where
  swap as bs ty = foldl (\acc (a, b) -> swap a b acc) ty (zip as bs)

instance Permute TyNom Tm where
  swap a b tm =
    case tm of
      Var x -> Var x
      Lam (Bind as (Bind xs body)) ->
        Lam (Bind (swap a b as) (Bind (swap a b xs) (swap a b body)))
      App t tys ts -> App (swap a b t) (swap a b tys) (swap a b ts)

-- Needed for alpha-equivalence when the bound name is a list of type vars.
instance Permute [TyNom] Tm where
  swap as bs tm = foldl (\acc (a, b) -> swap a b acc) tm (zip as bs)

-- Swap type variables through an inner term-binder so type variables in
-- parameter annotations are renamed as well.
instance Permute TyNom (Bind [(Nom, Ty)] Tm) where
  swap a b (Bind xs body) = Bind (swap a b xs) (swap a b body)

instance Permute [TyNom] (Bind [(Nom, Ty)] Tm) where
  swap as bs bnd = foldl (\acc (a, b) -> swap a b acc) bnd (zip as bs)

instance Permute Nom Tm where
  swap a b tm =
    case tm of
      Var x -> Var (swap a b x)
      Lam (Bind as (Bind xs body)) ->
        Lam (Bind as (Bind (swap a b xs) (swap a b body)))
      App t tys ts -> App (swap a b t) tys (swap a b ts)

instance Permute (Nom, Ty) Tm where
  swap (a, _) (b, _) = swap a b

instance Permute [(Nom, Ty)] Tm where
  swap as bs tm =
    foldl (\acc ((a, _), (b, _)) -> swap a b acc) tm (zip as bs)

instance Hash TyNom Ty where
  occursIn a ty =
    case ty of
      TTop -> False
      TBot -> False
      TVar b -> a == b
      TArr as r -> any (occursIn a) as || occursIn a r
      TForall (Bind as body) ->
        if a `elem` as
          then False
          else occursIn a body

instance Hash [TyNom] Ty where
  occursIn ns ty = any (\n -> occursIn n ty) ns

instance Hash TyNom (Bind [(Nom, Ty)] Tm) where
  occursIn a (Bind xs body) =
    any (occursIn a . snd) xs || occursIn a body

instance Hash [TyNom] (Bind [(Nom, Ty)] Tm) where
  occursIn ns bnd = any (\n -> occursIn n bnd) ns

instance Hash TyNom Tm where
  occursIn a tm =
    case tm of
      Var _ -> False
      Lam (Bind as (Bind xs body)) ->
        if a `elem` as
          then False
          else any (occursIn a . snd) xs || occursIn a body
      App t tys ts -> occursIn a t || any (occursIn a) tys || any (occursIn a) ts

instance Hash Nom Tm where
  occursIn a tm =
    case tm of
      Var b -> a == b
      Lam (Bind _ (Bind xs body)) ->
        if a `elem` map fst xs
          then False
          else occursIn a body
      App t _ ts -> occursIn a t || any (occursIn a) ts

instance Hash (Nom, Ty) Tm where
  occursIn (a, _) tm = occursIn a tm

instance Hash [(Nom, Ty)] Tm where
  occursIn ns tm = any (\(n, _) -> occursIn n tm) ns

--------------------------------------------------------------------------------
-- Smart constructors
--------------------------------------------------------------------------------

ttop :: Term Ty
ttop = ground TTop

tbot :: Term Ty
tbot = ground TBot

tvar :: Term TyNom -> Term Ty
tvar = lift1 (\a -> Ground (RTVar a))

tarr :: Term [Ty] -> Term Ty -> Term Ty
tarr = lift2 (\as b -> Ground (RTArr as b))

-- | Build @forall [a]. [A] -> B@.
tforall :: Term [TyNom] -> Term [Ty] -> Term Ty -> Term Ty
tforall as args res =
  lift1 (\bnd -> Ground (RTForall bnd)) (bind as (tarr args res))

var :: Term Nom -> Term Tm
var = lift1 (\x -> Ground (RVar x))

-- | Build @lam[a][x : A]. e@.
lam :: Term [TyNom] -> Term [(Nom, Ty)] -> Term Tm -> Term Tm
lam as xs body =
  lift1 (\bnd -> Ground (RLam bnd)) (bind as (bind xs body))

-- | Build @e @[A] ([e])@.
app :: Term Tm -> Term [Ty] -> Term [Tm] -> Term Tm
app = lift3 (\t tys ts -> Ground (RApp t tys ts))

lnil :: Repr a => Term [a]
lnil = ground []

lcons :: Repr a => Term a -> Term [a] -> Term [a]
lcons = lift2 (\x xs -> Ground (RListCons x xs))

tup :: (Repr a, Repr b) => Term a -> Term b -> Term (a, b)
tup = lift2 (\a b -> Ground (RTuple a b))
