{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE QualifiedDo #-}

-- | Standard nominal atom types and helpers.
module TypedRedex.Nominal.Prelude
  ( Nom(..)
  , TyNom(..)
  , nom
  , tynom
  , freshNom
  , freshTyNom
  ) where

import TypedRedex.Core.Term
import TypedRedex.DSL (RuleM)
import qualified TypedRedex.DSL as DSL
import TypedRedex.Nominal (NominalAtom(..), FreshName(..), Permute(..), Hash(..))
import TypedRedex.Pretty (Pretty(..), Doc(..), cycleNames)

--------------------------------------------------------------------------------
-- Nominal atoms
--------------------------------------------------------------------------------

newtype Nom = Nom { nomId :: Int }
  deriving (Eq, Ord, Show)

newtype TyNom = TyNom { tyNomId :: Int }
  deriving (Eq, Ord, Show)

instance NominalAtom Nom
instance NominalAtom TyNom

instance FreshName Nom where
  freshName = Nom

instance FreshName TyNom where
  freshName = TyNom

--------------------------------------------------------------------------------
-- Cross-namespace swap/hash defaults
--------------------------------------------------------------------------------

instance Permute Nom TyNom where
  swap _ _ x = x

instance Permute TyNom Nom where
  swap _ _ x = x

instance Hash Nom TyNom where
  occursIn _ _ = False

instance Hash TyNom Nom where
  occursIn _ _ = False

--------------------------------------------------------------------------------
-- Repr instances
--------------------------------------------------------------------------------

instance Repr Nom where
  data Reified Nom = NomR Int

  project (Nom n) = NomR n
  reify (NomR n) = Just (Nom n)
  quote (NomR n) = ("Nom" ++ show n, [])
  mapReified _ (NomR n) = NomR n

instance Repr TyNom where
  data Reified TyNom = TyNomR Int

  project (TyNom n) = TyNomR n
  reify (TyNomR n) = Just (TyNom n)
  quote (TyNomR n) = ("TyNom" ++ show n, [])
  mapReified _ (TyNomR n) = TyNomR n

--------------------------------------------------------------------------------
-- Pretty instances
--------------------------------------------------------------------------------

instance Pretty Nom where
  varNames = cycleNames ["x", "y", "z", "w"]
  prettyReified (NomR n) =
    pure (Doc (cycleNames ["x", "y", "z", "w"] !! n))

instance Pretty TyNom where
  varNames = cycleNames ["a", "b", "c", "d"]
  prettyReified (TyNomR n) =
    pure (Doc (cycleNames ["a", "b", "c", "d"] !! n))

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

nom :: Int -> Term Nom
nom = ground . Nom

tynom :: Int -> Term TyNom
tynom = ground . TyNom

freshNom :: RuleM ts (Term Nom)
freshNom = DSL.freshName

freshTyNom :: RuleM ts (Term TyNom)
freshTyNom = DSL.freshName
