{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}

-- | Freshness constraints for nominal logic.
--
-- This module provides the 'Hash' typeclass for checking if a name occurs
-- free in a term, and 'RedexHash' for interpreters that support lazy
-- freshness constraints.
--
-- In alphaKanren notation: @a # t@ means "a does not occur free in t".
module TypedRedex.Nominal.Hash
  ( -- * Hash Typeclass (Ground Checking)
    Hash(..)
    -- * RedexHash Typeclass (Lazy Constraints)
  , RedexHash(..)
  ) where

import TypedRedex.Core.Internal.Redex (Redex)
import TypedRedex.Core.Internal.Logic (LogicType)
import TypedRedex.DSL.Fresh (LTerm)
import TypedRedex.Nominal.Nom (NominalAtom)

--------------------------------------------------------------------------------
-- Hash Typeclass
--------------------------------------------------------------------------------

-- | Typeclass for checking if a name occurs free in a term.
--
-- Users implement this for their syntax types:
--
-- @
-- instance Hash TyNom Ty where
--   occursIn a TUnit = False
--   occursIn a (TVar b) = a == b
--   occursIn a (TArr t1 t2) = occursIn a t1 || occursIn a t2
--   occursIn a (TAll (Bind b body))
--     | a == b    = False  -- shadowed
--     | otherwise = occursIn a body
-- @
class Hash name term where
  -- | Check if name occurs free in term (when both are ground).
  -- Returns True if the name occurs free, False otherwise.
  occursIn :: name -> term -> Bool

-- | Base case: a name occurs in another name iff they're equal.
instance (Eq name, NominalAtom name) => Hash name name where
  occursIn a b = a == b

--------------------------------------------------------------------------------
-- RedexHash Typeclass
--------------------------------------------------------------------------------

-- | Typeclass for interpreters that support freshness constraints.
--
-- The 'hash' operation adds the constraint @a # t@ (a does not occur free in t).
-- If both arguments are ground, it checks immediately.
-- If either is a logic variable, it stores the constraint for later checking.
class Redex rel => RedexHash rel where
  -- | Add freshness constraint: a # t
  --
  -- Semantics:
  -- - If both ground: check immediately, fail if violated
  -- - If either is a logic variable: store constraint, check when unified
  --
  -- @
  -- hash (nom a) (tvar b)  -- a # b: succeeds if a ≠ b
  -- hash (nom a) ty        -- a # ty: succeeds if a not free in ty
  -- @
  hash :: (NominalAtom name, LogicType name, LogicType term, Hash name term)
       => LTerm name rel -> LTerm term rel -> rel ()
