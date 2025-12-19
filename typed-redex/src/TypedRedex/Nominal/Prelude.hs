{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Prelude for nominal logic with standard name types.
--
-- This module provides convenience types and functions for common use cases:
--
-- @
-- import TypedRedex
-- import TypedRedex.Nominal
-- import TypedRedex.Nominal.Prelude  -- for Nom, TyNom, freshNom, etc.
--
-- data Tm = Var Nom | Lam Ty (Bind Nom Tm) | App Tm Tm
--
-- -- In rules:
-- freshNom_ $ \x -> ...
-- (name, body) <- unbind bnd
-- @
--
-- For custom name types, use 'TypedRedex.Nominal' directly with 'RedexFresh'.
module TypedRedex.Nominal.Prelude
  ( -- * Standard Name Types
    Nom(..)
  , TyNom(..)
    -- * Fresh Name Generation
  , freshNom
  , freshTyNom
  , freshNom_
  , freshTyNom_
    -- * Convenience Unbind
  , unbind
  , unbindTy
    -- * Smart Constructors
  , nom
  , tynom
  ) where

import Control.Applicative (empty)
import TypedRedex.Core.Internal.Redex (Redex, RedexEval(..))
import TypedRedex.Core.Internal.Logic
import TypedRedex.DSL.Fresh (LTerm)
import TypedRedex.DSL.Type (con0)
import TypedRedex.Interp.Run (eval)
import TypedRedex.Interp.Subst (RedexFresh(..))
import TypedRedex.Interp.PrettyPrint (LogicVarNaming(..), VarNaming(..))
import TypedRedex.Nominal.Nom (NominalAtom(..))
import TypedRedex.Nominal.Bind (Bind(..), Permute(..), mkBind)
import TypedRedex.Nominal.Subst (Subst(..))
import TypedRedex.Nominal.Hash (Hash(..))

--------------------------------------------------------------------------------
-- Nominal Atom Types
--------------------------------------------------------------------------------

-- | A nominal atom for term variables.
--
-- Nom values are ground identifiers that represent variable names.
-- Two Noms are equal iff they have the same index.
newtype Nom = Nom { nomId :: Int }
  deriving (Eq, Ord)

instance Show Nom where
  show (Nom n) = "x" ++ show n

instance NominalAtom Nom

-- | A nominal atom for type variables.
--
-- TyNom values are ground identifiers that represent type variable names.
newtype TyNom = TyNom { tyNomId :: Int }
  deriving (Eq, Ord)

instance Show TyNom where
  show (TyNom n) = "α" ++ show n

instance NominalAtom TyNom

--------------------------------------------------------------------------------
-- LogicType Instances
--------------------------------------------------------------------------------

instance LogicVarNaming Nom where
  varNaming = VarNaming "X" (\i -> "x?" ++ show i)

instance LogicType Nom where
  data Reified Nom var = NomR Int

  project (Nom n) = NomR n

  reify (NomR n) = Just (Nom n)

  -- NomR doesn't depend on var, so we can use a simple implementation
  quote (NomR n) = (con0 ("x" ++ show n) (NomR n), [])

  unifyVal _ (NomR a) (NomR b)
    | a == b    = pure ()
    | otherwise = empty

  derefVal _ (NomR n) = pure (Nom n)


instance LogicVarNaming TyNom where
  varNaming = VarNaming "A" (\i -> "α?" ++ show i)

instance LogicType TyNom where
  data Reified TyNom var = TyNomR Int

  project (TyNom n) = TyNomR n

  reify (TyNomR n) = Just (TyNom n)

  quote (TyNomR n) = (con0 ("α" ++ show n) (TyNomR n), [])

  unifyVal _ (TyNomR a) (TyNomR b)
    | a == b    = pure ()
    | otherwise = empty

  derefVal _ (TyNomR n) = pure (TyNom n)

--------------------------------------------------------------------------------
-- Cross-namespace Permute instances
--------------------------------------------------------------------------------

-- Swapping Nom doesn't affect TyNom
instance Permute Nom TyNom where
  swap _ _ x = x

-- Swapping TyNom doesn't affect Nom
instance Permute TyNom Nom where
  swap _ _ x = x

--------------------------------------------------------------------------------
-- Cross-namespace Subst instances
--------------------------------------------------------------------------------

-- Substituting Nom doesn't affect TyNom
instance Subst Nom TyNom where
  subst _ _ y = y

-- Substituting TyNom doesn't affect Nom
instance Subst TyNom Nom where
  subst _ _ y = y

--------------------------------------------------------------------------------
-- Cross-namespace Hash instances
--------------------------------------------------------------------------------

-- Nom never occurs free in TyNom (different namespaces)
instance Hash Nom TyNom where
  occursIn _ _ = False

-- TyNom never occurs free in Nom (different namespaces)
instance Hash TyNom Nom where
  occursIn _ _ = False

--------------------------------------------------------------------------------
-- Fresh Name Generation
--------------------------------------------------------------------------------

-- | Generate a fresh term variable name.
freshNom :: RedexFresh rel => rel Nom
freshNom = Nom <$> freshInt

-- | Generate a fresh type variable name.
freshTyNom :: RedexFresh rel => rel TyNom
freshTyNom = TyNom <$> freshInt

-- | CPS version of 'freshNom'.
freshNom_ :: RedexFresh rel => (Nom -> rel a) -> rel a
freshNom_ k = freshNom >>= k

-- | CPS version of 'freshTyNom'.
freshTyNom_ :: RedexFresh rel => (TyNom -> rel a) -> rel a
freshTyNom_ k = freshTyNom >>= k

--------------------------------------------------------------------------------
-- Convenience Unbind
--------------------------------------------------------------------------------

-- | Open a term binder (Bind Nom) with a fresh name.
unbind :: (RedexFresh rel, RedexEval rel, LogicType body, Permute Nom body)
       => LTerm (Bind Nom body) rel
       -> rel (LTerm Nom rel, LTerm body rel)
unbind bndL = do
  Bind oldName body <- eval bndL
  fresh <- freshNom
  let swappedBody = swap oldName fresh body
  pure (Ground (project fresh), Ground (project swappedBody))

-- | Open a type binder (Bind TyNom) with a fresh name.
unbindTy :: (RedexFresh rel, RedexEval rel, LogicType body, Permute TyNom body)
         => LTerm (Bind TyNom body) rel
         -> rel (LTerm TyNom rel, LTerm body rel)
unbindTy bndL = do
  Bind oldName body <- eval bndL
  fresh <- freshTyNom
  let swappedBody = swap oldName fresh body
  pure (Ground (project fresh), Ground (project swappedBody))

--------------------------------------------------------------------------------
-- Smart Constructors
--------------------------------------------------------------------------------

-- | Create a ground term variable reference.
nom :: Nom -> LTerm Nom rel
nom = Ground . project

-- | Create a ground type variable reference.
tynom :: TyNom -> LTerm TyNom rel
tynom = Ground . project
