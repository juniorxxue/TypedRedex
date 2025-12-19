{-# LANGUAGE DefaultSignatures #-}

-- | Nominal atom typeclass for lambda binding.
--
-- This module provides the 'NominalAtom' typeclass that defines the requirements
-- for name types that can be used with 'Bind'.
--
-- For standard name types ('Nom', 'TyNom'), see "TypedRedex.Nominal.Prelude".
module TypedRedex.Nominal.Nom
  ( NominalAtom(..)
  ) where

import TypedRedex.Core.Internal.Logic (LogicType)

--------------------------------------------------------------------------------
-- Nominal Atom Typeclass
--------------------------------------------------------------------------------

-- | Typeclass for nominal atom types (variable names).
--
-- A nominal atom is a ground identifier used for variable binding.
-- Types that implement this class can be used with 'Bind'.
--
-- Requirements:
-- - 'Eq' for comparing names (needed for alpha-equivalence)
-- - 'LogicType' for use in logic terms
-- - Self-swapping: @swap a b a == b@ and @swap a b b == a@
--
-- Example: defining a custom name type:
--
-- @
-- newtype KindNom = KindNom Int deriving (Eq, Ord)
--
-- instance NominalAtom KindNom
--
-- instance LogicType KindNom where
--   ...
--
-- freshKindNom :: RedexFresh rel => rel KindNom
-- freshKindNom = KindNom \<$\> freshInt
-- @
class (Eq name, LogicType name) => NominalAtom name where
  -- | Swap two names in a name. This is the base case for permutation.
  swapAtom :: name -> name -> name -> name
  swapAtom a b x
    | x == a    = b
    | x == b    = a
    | otherwise = x
