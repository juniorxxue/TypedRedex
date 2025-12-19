{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Capture-avoiding substitution for nominal binders.
--
-- This module provides 'Substo', a relational substitution that uses
-- the '#' (hash) constraint to ensure capture-avoidance.
--
-- = Why Relational?
--
-- Pure substitution like @[β/α](∀β. α → β)@ naively gives @∀β. β → β@,
-- which is WRONG because the free β got captured by the binder.
--
-- The correct result is @∀γ. β → γ@ where γ is fresh.
--
-- Relational substitution with hash constraints handles this:
-- @
-- substo α (∀β. α → β) β ?result
--   -- Picks fresh γ where γ # β (γ doesn't occur in replacement)
--   -- Result: ∀γ. β → γ
-- @
--
-- = Usage
--
-- Users implement 'Substo' for their syntax types. The key for binders is:
--
-- 1. Pick a fresh binder name
-- 2. Use 'hash' to ensure the fresh name doesn't occur in the replacement
-- 3. Swap the old binder to the fresh one, then substitute
--
-- See examples/system-f for a complete example.
module TypedRedex.Nominal.Subst
  ( -- * Relational Substitution
    Substo(..)
    -- * Legacy Pure Substitution (use with caution)
  , Subst(..)
  , substBind
  ) where

import Control.Applicative (empty)
import TypedRedex.Core.Internal.Redex (Redex(..))
import TypedRedex.Core.Internal.Relation (conde, (<=>))
import TypedRedex.Core.Internal.Logic (LogicType(..))
import TypedRedex.DSL.Fresh (LTerm)
import TypedRedex.Interp.Subst (RedexFresh(..))
import TypedRedex.Nominal.Nom (NominalAtom(..))
import TypedRedex.Nominal.Bind (Bind(..), Permute(..))
import TypedRedex.Nominal.Hash (Hash(..), RedexHash(..))

--------------------------------------------------------------------------------
-- Relational Substitution (Capture-Avoiding)
--------------------------------------------------------------------------------

-- | Typeclass for capture-avoiding relational substitution.
--
-- @substo name body replacement result@ means @[replacement/name]body = result@
--
-- Unlike pure 'Subst', this uses hash constraints to prevent capture.
--
-- Users implement this for their syntax types. For binder cases:
--
-- @
-- -- For ∀ types:
-- substo aL (tall bnd) replL resultL = conde
--   [ do -- Shadowed case
--        (alphaL, tyL) <- unbindTy bnd
--        aL <=> alphaL
--        resultL <=> tall bnd
--   , do -- Substitute case
--        freshTyNom_ $ \\fresh -> do
--          (alphaL, tyL) <- unbindTy bnd
--          hash aL alphaL                       -- a ≠ bound var
--          hash (tynom fresh) replL             -- fresh # replacement
--          -- Evaluate for swapping
--          alpha <- eval alphaL
--          ty <- eval tyL
--          let swappedTy = swap alpha fresh ty  -- Rename binder
--          substo aL (Ground (project swappedTy)) replL resultTy
--          resultL <=> tall (bind fresh resultTy)
--   ]
-- @
class Substo name body where
  -- | Relational substitution: @[replacement/name]body = result@
  substo :: (RedexFresh rel, RedexHash rel, Redex rel)
         => LTerm name rel    -- ^ Name to substitute for
         -> LTerm body rel    -- ^ Body to substitute in
         -> LTerm body rel    -- ^ Replacement term
         -> LTerm body rel    -- ^ Result
         -> rel ()

--------------------------------------------------------------------------------
-- Base Instance: Name in Name
--------------------------------------------------------------------------------

-- | Substituting a name for the same name type.
--
-- @[replacement/a]b = replacement@ if @a == b@
-- @[replacement/a]b = b@ if @a ≠ b@ (i.e., @a # b@)
instance (NominalAtom name, LogicType name, Hash name name) => Substo name name where
  substo aL bL replL resultL = conde
    [ do -- a == b: result is replacement
        aL <=> bL
        resultL <=> replL
    , do -- a ≠ b: result is b unchanged
        hash aL bL  -- a # b (they're different)
        resultL <=> bL
    ]

--------------------------------------------------------------------------------
-- Legacy Pure Substitution (No Capture Avoidance)
--------------------------------------------------------------------------------

-- | DEPRECATED: Pure substitution WITHOUT capture avoidance.
--
-- WARNING: This does NOT handle capture correctly!
-- Use 'Substo' for correct capture-avoiding substitution.
--
-- Kept for backward compatibility and simple cases where capture can't occur.
class Subst name term where
  -- | Substitute: @[arg/x]term@
  --
  -- Replace all free occurrences of @x@ in @term@ with @arg@.
  subst :: name -> term -> term -> term

-- | DEPRECATED: Pure substitution under a binder.
--
-- WARNING: This does NOT handle capture correctly!
--
-- If the binder binds the same name we're substituting, do nothing (shadowing).
-- Otherwise, substitute in the body (potentially causing capture!).
substBind :: (NominalAtom name, Subst name body) => name -> body -> Bind name body -> Bind name body
substBind x arg (Bind y body)
  | x == y    = Bind y body       -- x is shadowed by y
  | otherwise = Bind y (subst x arg body)  -- WARNING: May capture!

-- | Pure substitution for names.
instance NominalAtom name => Subst name name where
  subst x arg y
    | x == y    = arg
    | otherwise = y
