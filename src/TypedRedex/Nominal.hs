-- | Nominal logic support: atoms, swapping, freshness.
module TypedRedex.Nominal
  ( NominalAtom(..)
  , Permute(..)
  , Hash(..)
  , FreshName(..)
  ) where

-- | Nominal atom types (names).
class (Eq name) => NominalAtom name where
  -- | Swap two names inside a name.
  swapAtom :: name -> name -> name -> name
  swapAtom a b x
    | x == a = b
    | x == b = a
    | otherwise = x

-- | Apply a swap to a term.
class Permute name term where
  swap :: name -> name -> term -> term

-- Nominal atoms swap themselves.
instance NominalAtom name => Permute name name where
  swap = swapAtom

-- | Freshness: name does not occur in term.
class NominalAtom name => Hash name term where
  occursIn :: name -> term -> Bool

-- Names occur in themselves.
instance NominalAtom name => Hash name name where
  occursIn a b = a == b

-- | Construct fresh names from integer indices.
class NominalAtom name => FreshName name where
  freshName :: Int -> name
