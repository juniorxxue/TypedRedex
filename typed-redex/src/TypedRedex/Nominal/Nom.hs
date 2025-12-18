{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}

-- | Nominal atoms for lambda binding.
--
-- This module provides the 'Nom' and 'TyNom' types representing
-- nominal atoms (names) for term and type variables respectively.
-- Unlike logic variables, nominal atoms are ground values.
module TypedRedex.Nominal.Nom
  ( -- * Nominal Atom Types
    Nom(..)
  , TyNom(..)
    -- * Fresh Name Generation
  , NomState(..)
  , initialNomState
  , genFreshNom
  , genFreshTyNom
  ) where

import Control.Applicative (empty)
import TypedRedex.Core.Internal.Logic
import TypedRedex.DSL.Type (con0)
import TypedRedex.Interp.PrettyPrint (LogicVarNaming(..), VarNaming(..))

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

-- | A nominal atom for type variables.
--
-- TyNom values are ground identifiers that represent type variable names.
newtype TyNom = TyNom { tyNomId :: Int }
  deriving (Eq, Ord)

instance Show TyNom where
  show (TyNom n) = "α" ++ show n

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
-- Fresh Name Generation State
--------------------------------------------------------------------------------

-- | State for generating fresh nominal atoms.
data NomState = NomState
  { nextNom   :: !Int  -- ^ Counter for term variable names
  , nextTyNom :: !Int  -- ^ Counter for type variable names
  }

-- | Initial state with counters at 0.
initialNomState :: NomState
initialNomState = NomState 0 0

-- | Generate a fresh term variable name.
genFreshNom :: NomState -> (Nom, NomState)
genFreshNom s = (Nom (nextNom s), s { nextNom = nextNom s + 1 })

-- | Generate a fresh type variable name.
genFreshTyNom :: NomState -> (TyNom, NomState)
genFreshTyNom s = (TyNom (nextTyNom s), s { nextTyNom = nextTyNom s + 1 })
