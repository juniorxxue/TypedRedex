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
    -- * Helpers for Binders
  , substBind
  , substTyBind
  ) where

import TypedRedex.Nominal.Nom
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
-- Helpers for Binders
--------------------------------------------------------------------------------

-- | Substitute under a term binder.
--
-- If the binder binds the same name we're substituting, do nothing (shadowing).
-- Otherwise, substitute in the body.
--
-- @
-- substBind x arg (Bind y body)
--   | x == y    = Bind y body        -- Shadowed
--   | otherwise = Bind y (subst x arg body)
-- @
substBind :: Subst Nom body => Nom -> body -> Bind body -> Bind body
substBind x arg (Bind y body)
  | x == y    = Bind y body       -- x is shadowed by y
  | otherwise = Bind y (subst x arg body)

-- | Substitute under a type binder.
--
-- Similar to 'substBind' but for type variable binders.
substTyBind :: Subst TyNom body => TyNom -> body -> TyBind body -> TyBind body
substTyBind alpha arg (TyBind beta body)
  | alpha == beta = TyBind beta body    -- Shadowed
  | otherwise     = TyBind beta (subst alpha arg body)

--------------------------------------------------------------------------------
-- Default Instances
--------------------------------------------------------------------------------

-- | Substituting a Nom for a Nom just compares.
instance Subst Nom Nom where
  subst x arg y
    | x == y    = arg
    | otherwise = y

-- | Substituting a TyNom for a TyNom just compares.
instance Subst TyNom TyNom where
  subst alpha arg beta
    | alpha == beta = arg
    | otherwise     = beta

-- | Nom substitution doesn't affect TyNom.
instance Subst Nom TyNom where
  subst _ _ y = y

-- | TyNom substitution doesn't affect Nom.
instance Subst TyNom Nom where
  subst _ _ y = y
