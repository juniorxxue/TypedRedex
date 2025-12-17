{-# LANGUAGE Rank2Types #-}

-- | Shared substitution infrastructure for interpreters.
--
-- This module provides the common variable representation and helper
-- functions used by both SubstRedex and TracingRedex interpreters.
--
-- = Design
--
-- Both interpreters use integer-based variable representation.
-- This module provides the shared `VarRepr` type and utility functions.
-- Each interpreter defines its own state type that uses these primitives.
module TypedRedex.Core.Internal.SubstCore
  ( -- * Variable representation
    VarRepr
    -- * Display helper
  , displayVarInt
  ) where

-- | Variable representation: simple integers.
--
-- Both SubstRedex and TracingRedex use Int-based variables.
type VarRepr = Int

-- | Display a variable given its integer representation.
displayVarInt :: VarRepr -> String
displayVarInt n = "x" ++ show n
