{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

-- | Nominal Logic for TypedRedex.
--
-- This module provides support for lambda binding with named variables
-- instead of de Bruijn indices, based on alphaKanren-style nominal logic.
--
-- = Quick Start
--
-- For most users, import both this module and the Prelude:
--
-- @
-- import TypedRedex
-- import TypedRedex.Nominal
-- import TypedRedex.Nominal.Prelude  -- for Nom, TyNom, freshNom, etc.
--
-- -- Define syntax with nominal atoms
-- data Tm = Var Nom | Lam Ty (Bind Nom Tm) | App Tm Tm
--
-- -- In rules, use freshNom and unbind
-- typeofLam = rule \"T-Lam\" $ fresh2 $ \\ctx tyA -> do
--   freshNom_ $ \\x -> fresh2 $ \\body tyB -> do
--     concl $ typeof ctx (lam tyA (bind x body)) (tarr tyA tyB)
--     prem $ typeof (extend (nom x) tyA ctx) body tyB
-- @
--
-- = Hash Constraints (Freshness)
--
-- The 'hash' function asserts @a # t@ (\"a does not occur free in t\"):
--
-- @
-- hash (nom x) term  -- x # term
-- @
--
-- = Capture-Avoiding Substitution
--
-- Use 'Substo' for capture-avoiding substitution. See "TypedRedex.Nominal.Subst".
--
-- = Custom Name Types
--
-- For custom name types, use 'RedexFresh' and 'unbindWith':
--
-- @
-- newtype KindNom = KindNom Int deriving (Eq, Ord)
-- instance NominalAtom KindNom
-- instance LogicType KindNom where ...
--
-- freshKindNom :: RedexFresh rel => rel KindNom
-- freshKindNom = KindNom \<$\> freshInt
--
-- freshKindNom_ :: RedexFresh rel => (KindNom -> rel a) -> rel a
-- freshKindNom_ k = freshKindNom >>= k
--
-- unbindKind = unbindWith freshKindNom_
-- @
module TypedRedex.Nominal
  ( -- * Nominal Atom Typeclass
    NominalAtom(..)
    -- * Binder Type
  , Bind(..)
    -- * Permutation
  , Permute(..)
    -- * Hash Constraints (Freshness)
  , Hash(..)
  , RedexHash(..)
    -- * Relational Substitution (Capture-Avoiding)
  , Substo(..)
    -- * Legacy Pure Substitution (use with caution)
  , Subst(..)
  , substBind
    -- * Fresh Name Generation
  , RedexFresh(..)
    -- * High-Level API (Generic)
  , unbindWith
  , instantiate
  , instantiateTo
    -- * Smart Constructor
  , bind
  ) where

import TypedRedex.Core.Internal.Redex
import TypedRedex.Core.Internal.Logic
import TypedRedex.Core.Internal.Relation ((<=>))
import TypedRedex.DSL.Fresh (LTerm)
import TypedRedex.Interp.Run (eval)
import TypedRedex.Interp.Subst (RedexFresh(..))
import TypedRedex.Nominal.Nom
import TypedRedex.Nominal.Bind
import TypedRedex.Nominal.Subst
import TypedRedex.Nominal.Hash

--------------------------------------------------------------------------------
-- High-Level API (Generic)
--------------------------------------------------------------------------------

-- | Open a binder with a fresh name (generic version).
--
-- Takes a fresh name generator as the first argument.
--
-- @
-- -- With standard types from Prelude:
-- unbindWith freshNom_ bnd   -- for Bind Nom body
-- unbindWith freshTyNom_ bnd -- for Bind TyNom body
--
-- -- With custom types:
-- unbindWith freshKindNom_ bnd -- for Bind KindNom body
-- @
unbindWith :: (RedexEval rel, NominalAtom name, LogicType body, Permute name body)
           => (forall a. (name -> rel a) -> rel a)  -- ^ Fresh name generator (CPS)
           -> LTerm (Bind name body) rel
           -> rel (LTerm name rel, LTerm body rel)
unbindWith freshGen bndL = do
  -- Evaluate to get the concrete binder
  Bind oldName body <- eval bndL
  -- Generate a fresh name and swap
  freshGen $ \fresh -> do
    let swappedBody = swap oldName fresh body
    pure (Ground (project fresh), Ground (project swappedBody))

-- | Instantiate a binder with an argument (capture-avoiding substitution).
--
-- @
-- result <- instantiate bnd arg  -- [arg/x]body where bnd = Bind x body
-- @
instantiate :: (RedexEval rel, NominalAtom name, LogicType body, Permute name body, Subst name body)
            => LTerm (Bind name body) rel
            -> LTerm body rel
            -> rel (LTerm body rel)
instantiate bndL argL = do
  bnd <- eval bndL
  arg <- eval argL
  let Bind x body = bnd
  pure (Ground (project (subst x arg body)))

-- | Instantiate a binder and unify result with a logic variable.
--
-- @
-- instantiateTo bnd arg result  -- result = [arg/x]body
-- @
instantiateTo :: (Redex rel, RedexEval rel, NominalAtom name, LogicType body, Permute name body, Subst name body)
              => LTerm (Bind name body) rel
              -> LTerm body rel
              -> LTerm body rel
              -> rel ()
instantiateTo bnd arg result = do
  resultVal <- instantiate bnd arg
  result <=> resultVal

--------------------------------------------------------------------------------
-- Smart Constructor
--------------------------------------------------------------------------------

-- | Create a binder (works with logic variable bodies).
--
-- @
-- bind x body  -- creates Bind x body
-- @
bind :: (NominalAtom name, LogicType body, Permute name body)
     => name -> LTerm body rel -> LTerm (Bind name body) rel
bind n b = mkBind n b
