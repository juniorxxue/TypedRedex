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
-- @
-- import TypedRedex
-- import TypedRedex.Nominal
--
-- -- Define syntax with nominal atoms
-- data Tm = Var Nom | Lam Ty (Bind Tm) | App Tm Tm
--
-- -- In rules, use freshNom and unbind
-- typeofLam = rule "T-Lam" $ do
--   [ctx, tyA, tyB, bnd] <- freshVars
--   concl $ typeof ctx (lam tyA bnd) (tarr tyA tyB)
--   (x, body) <- unbind bnd
--   prem $ typeof (extend x tyA ctx) body tyB
-- @
--
-- = Design
--
-- * 'Nom' and 'TyNom' are ground nominal atoms (not logic variables)
-- * 'Bind' and 'TyBind' are binders with alpha-equivalence in unification
-- * 'freshNom' generates fresh atoms
-- * 'unbind' opens a binder with a fresh name
-- * 'instantiate' performs capture-avoiding substitution
module TypedRedex.Nominal
  ( -- * Nominal Atom Types
    Nom(..)
  , TyNom(..)
    -- * Binder Types
  , Bind(..)
  , TyBind(..)
    -- * Permutation
  , Permute(..)
    -- * Substitution
  , Subst(..)
  , substBind
  , substTyBind
    -- * Nominal Operations Typeclass
  , RedexNom(..)
    -- * High-Level API
  , unbind
  , unbindTy
  , instantiate
  , instantiateTy
  , instantiateTo
  , instantiateTyTo
    -- * Smart Constructors
  , bind
  , bindTy
  , nom
  , tynom
  ) where

import TypedRedex.Core.Internal.Redex
import TypedRedex.Core.Internal.Logic
import TypedRedex.Core.Internal.Relation ((<=>))
import TypedRedex.DSL.Fresh (LTerm)
import TypedRedex.Interp.Run (eval)
import TypedRedex.Interp.Subst (RedexNom(..))
import TypedRedex.Nominal.Nom
import TypedRedex.Nominal.Bind
import TypedRedex.Nominal.Subst

--------------------------------------------------------------------------------
-- Fresh Name Generation
--------------------------------------------------------------------------------

-- | Generate a fresh term variable name as a logic term.
freshNom :: RedexNom rel => rel (LTerm Nom rel)
freshNom = freshNom_ (pure . Ground . project)

-- | Generate a fresh type variable name as a logic term.
freshTyNom :: RedexNom rel => rel (LTerm TyNom rel)
freshTyNom = freshTyNom_ (pure . Ground . project)

--------------------------------------------------------------------------------
-- High-Level API
--------------------------------------------------------------------------------

-- | Open a term binder with a fresh name.
--
-- Returns the fresh name and the body.
--
-- @
-- (x, body) <- unbind bnd
-- @
unbind :: (RedexNom rel, RedexEval rel, LogicType body, Permute Nom body)
       => LTerm (Bind body) rel
       -> rel (LTerm Nom rel, LTerm body rel)
unbind bndL = do
  -- Evaluate to get the concrete binder
  Bind oldName body <- eval bndL
  -- Generate a fresh name and swap
  freshNom_ $ \fresh -> do
    let swappedBody = swap oldName fresh body
    pure (Ground (project fresh), Ground (project swappedBody))

-- | Open a type binder with a fresh name.
unbindTy :: (RedexNom rel, RedexEval rel, LogicType body, Permute TyNom body)
         => LTerm (TyBind body) rel
         -> rel (LTerm TyNom rel, LTerm body rel)
unbindTy bndL = do
  -- Evaluate to get the concrete binder
  TyBind oldName body <- eval bndL
  -- Generate a fresh name and swap
  freshTyNom_ $ \fresh -> do
    let swappedBody = swap oldName fresh body
    pure (Ground (project fresh), Ground (project swappedBody))

-- | Instantiate a term binder with a term (capture-avoiding substitution).
--
-- @
-- result <- instantiate bnd arg  -- [arg/x]body where bnd = Bind x body
-- @
instantiate :: (RedexNom rel, RedexEval rel, LogicType body, Permute Nom body, Subst Nom body)
            => LTerm (Bind body) rel
            -> LTerm body rel
            -> rel (LTerm body rel)
instantiate bndL argL = do
  -- Evaluate the binder to get the name and body
  bnd <- eval bndL
  arg <- eval argL
  let Bind x body = bnd
  pure (Ground (project (subst x arg body)))

-- | Instantiate a type binder with a type.
instantiateTy :: (RedexNom rel, RedexEval rel, LogicType body, Permute TyNom body, Subst TyNom body)
              => LTerm (TyBind body) rel
              -> LTerm body rel
              -> rel (LTerm body rel)
instantiateTy bndL argL = do
  bnd <- eval bndL
  arg <- eval argL
  let TyBind alpha body = bnd
  pure (Ground (project (subst alpha arg body)))

-- | Instantiate a term binder and unify result with a logic variable.
--
-- @
-- instantiateTo bnd arg result  -- result = [arg/x]body
-- @
instantiateTo :: (Redex rel, RedexNom rel, RedexEval rel, LogicType body, Permute Nom body, Subst Nom body)
              => LTerm (Bind body) rel
              -> LTerm body rel
              -> LTerm body rel
              -> rel ()
instantiateTo bnd arg result = do
  resultVal <- instantiate bnd arg
  result <=> resultVal

-- | Instantiate a type binder and unify result with a logic variable.
--
-- @
-- instantiateTyTo tyBnd tyArg result  -- result = [tyArg/alpha]body
-- @
instantiateTyTo :: (Redex rel, RedexNom rel, RedexEval rel, LogicType body, Permute TyNom body, Subst TyNom body)
                => LTerm (TyBind body) rel
                -> LTerm body rel
                -> LTerm body rel
                -> rel ()
instantiateTyTo bnd arg result = do
  resultVal <- instantiateTy bnd arg
  result <=> resultVal

--------------------------------------------------------------------------------
-- Smart Constructors
--------------------------------------------------------------------------------

-- | Create a term binder (works with logic variable bodies).
bind :: (LogicType body, Permute Nom body) => Nom -> LTerm body rel -> LTerm (Bind body) rel
bind n b = mkBind n b

-- | Create a type binder (works with logic variable bodies).
bindTy :: (LogicType body, Permute TyNom body) => TyNom -> LTerm body rel -> LTerm (TyBind body) rel
bindTy n b = mkTyBind n b

-- | Create a ground term variable reference.
nom :: Nom -> LTerm Nom rel
nom = Ground . project

-- | Create a ground type variable reference.
tynom :: TyNom -> LTerm TyNom rel
tynom = Ground . project
