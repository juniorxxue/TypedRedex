{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}

-- | Substitution for nominal binders.
--
-- This module provides the 'Subst' typeclass that users implement
-- for their syntax types to enable 'instantiate'.
module TypedRedex.Nominal.Subst
  ( -- * Substitution Typeclass
    Subst(..)
    -- * Helper for Binders
  , substBind
  ) where

import TypedRedex.Nominal.Nom (NominalAtom(..))
import TypedRedex.Nominal.Bind

--------------------------------------------------------------------------------
-- Substitution Typeclass
--------------------------------------------------------------------------------

-- | Typeclass for substituting a term for a name.
--
-- Users implement this for their syntax types:
--
-- @
-- instance Subst Nom Tm where
--   subst x arg (Var y)
--     | x == y    = arg
--     | otherwise = Var y
--   subst x arg (Lam ty bnd) = Lam ty (substBind x arg bnd)
--   subst x arg (App e1 e2)  = App (subst x arg e1) (subst x arg e2)
-- @
class Subst name term where
  -- | Substitute: @[arg/x]term@
  --
  -- Replace all free occurrences of @x@ in @term@ with @arg@.
  subst :: name -> term -> term -> term

--------------------------------------------------------------------------------
-- Helper for Binders
--------------------------------------------------------------------------------

-- | Substitute under a binder.
--
-- If the binder binds the same name we're substituting, do nothing (shadowing).
-- Otherwise, substitute in the body.
--
-- @
-- substBind x arg (Bind y body)
--   | x == y    = Bind y body        -- Shadowed
--   | otherwise = Bind y (subst x arg body)
-- @
substBind :: (NominalAtom name, Subst name body) => name -> body -> Bind name body -> Bind name body
substBind x arg (Bind y body)
  | x == y    = Bind y body       -- x is shadowed by y
  | otherwise = Bind y (subst x arg body)

--------------------------------------------------------------------------------
-- Default Instances
--------------------------------------------------------------------------------

-- | Substituting a name for the same name type just compares.
instance NominalAtom name => Subst name name where
  subst x arg y
    | x == y    = arg
    | otherwise = y
