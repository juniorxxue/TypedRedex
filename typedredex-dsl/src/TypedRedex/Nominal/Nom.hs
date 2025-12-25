-- | Nominal atom typeclass for lambda binding.
--
-- This module re-exports 'NominalAtom' from the logic layer.
-- For standard name types ('Nom', 'TyNom'), see "TypedRedex.Nominal.Prelude".
module TypedRedex.Nominal.Nom
  ( NominalAtom(..)
  ) where

import TypedRedex.Logic.Nominal (NominalAtom(..))
