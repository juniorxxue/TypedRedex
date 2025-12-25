-- | Shared substitution infrastructure for interpreters.
--
-- This module provides the common variable representation and helper
-- functions used by substitution-based interpreters.
module TypedRedex.Logic.SubstCore
  ( -- * Variable representation
    VarRepr
    -- * Display helper
  , displayVarInt
  ) where

-- | Variable representation: simple integers.
type VarRepr = Int

-- | Display a variable given its integer representation.
displayVarInt :: VarRepr -> String
displayVarInt n = "x" ++ show n
