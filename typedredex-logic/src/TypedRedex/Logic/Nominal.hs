{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

-- | Core nominal type classes for the logic layer.
--
-- This module provides the basic type classes for nominal logic:
--
-- * 'NominalAtom' - types that can be used as bound names
-- * 'Permute' - name swapping for alpha-equivalence
-- * 'Hash' - freshness checking (name-term freshness relation)
--
-- These are separate from the DSL layer to allow the 'RedexHash' class
-- in 'TypedRedex.Logic.Redex' to reference them.
module TypedRedex.Logic.Nominal
  ( -- * Nominal Atom Typeclass
    NominalAtom(..)
    -- * Permutation (Name Swapping)
  , Permute(..)
    -- * Hash (Freshness)
  , Hash(..)
  ) where

import TypedRedex.Logic.Term (LogicType)

--------------------------------------------------------------------------------
-- Nominal Atom Typeclass
--------------------------------------------------------------------------------

-- | Typeclass for nominal atom types (variable names).
--
-- A nominal atom is a ground identifier used for variable binding.
-- Types that implement this class can be used with binders.
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

--------------------------------------------------------------------------------
-- Permutation Typeclass
--------------------------------------------------------------------------------

-- | Typeclass for applying name permutations (swaps).
--
-- This is needed for alpha-equivalence: when unifying @Bind a t@ with @Bind b u@
-- where @a /= b@, we swap @a <-> b@ in @u@ before unifying @t@ with the result.
class Permute name term where
  -- | Apply a swap: replace all occurrences of @a@ with @b@ and vice versa.
  swap :: name -> name -> term -> term

-- NominalAtom instances swap themselves
instance NominalAtom name => Permute name name where
  swap = swapAtom

--------------------------------------------------------------------------------
-- Hash (Freshness) Typeclass
--------------------------------------------------------------------------------

-- | Typeclass for checking if a name occurs in a term.
--
-- The @occursIn@ method checks whether a name occurs free in a term.
-- This is the semantic basis for the hash (freshness) constraint @a # t@:
-- the constraint holds when @occursIn a t == False@.
class (NominalAtom name) => Hash name term where
  -- | Check if a name occurs free in a term.
  --
  -- @occursIn a t@ returns 'True' if @a@ appears free in @t@.
  occursIn :: name -> term -> Bool

-- | Names occur in themselves.
instance NominalAtom name => Hash name name where
  occursIn a b = a == b
