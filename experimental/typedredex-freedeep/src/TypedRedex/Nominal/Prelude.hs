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
  , unbind2
  ) where

import Data.Typeable (Typeable)
import TypedRedex.Core.Term
import TypedRedex.DSL (RuleM, (===))
import qualified TypedRedex.DSL as DSL
import TypedRedex.Nominal (NominalAtom(..), FreshName(..), Permute(..), Hash(..))
import TypedRedex.Nominal.Bind (Bind, bind)
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

-- | Open two binders with the same fresh name.
unbind2
  :: (NominalAtom name, FreshName name, Repr name, Repr body1, Repr body2,
      Typeable name, Typeable body1, Typeable body2,
      Permute name body1, Permute name body2)
  => Term (Bind name body1)
  -> Term (Bind name body2)
  -> RuleM ts (Term name, Term body1, Term body2)
unbind2 bnd1 bnd2 = DSL.do
  name <- DSL.freshName
  (body1, body2) <- DSL.fresh
  (===) (bind name body1) bnd1
  (===) (bind name body2) bnd2
  DSL.return (name, body1, body2)
