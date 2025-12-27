{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DefaultSignatures #-}

-- | Core logic term representation for TypedRedex Free.
--
-- This is a standalone module for the free monad experimental project.
--
-- = Class Hierarchy
--
-- @
-- LogicRepr a         -- Minimal: Reified, project, reify, quote, display
--   │
--   └── LogicType a   -- Full: unifyVal, derefVal
-- @
module TypedRedex.Free.Logic
  ( -- * Logic Terms
    Logic(..)
  , Var(..)
    -- * Logic Types (class hierarchy)
  , LogicRepr(..)
  , LogicType(..)
    -- * Higher-rank Helpers
  , Unifier
  , Evaluator
    -- * Child Traversal
  , Field(..)
    -- * Interpreter Classes
  , Redex(..)
    -- * Core Types
  , Goal
  , FreshType(..)
    -- * Re-exports
  , Alternative(empty, (<|>))
  ) where

import Control.Applicative (Alternative(empty, (<|>)))
import Data.Kind (Type)
import Data.Proxy (Proxy)
import Data.Typeable (Typeable)

--------------------------------------------------------------------------------
-- Logic Terms and Variables
--------------------------------------------------------------------------------

-- | A typed logic variable for values of type @a@.
newtype Var (a :: Type) (var :: Type -> Type) = Var
  { unVar :: var (Logic a var)
  }

-- | A logic term: either a free variable or a ground value.
data Logic (a :: Type) (var :: Type -> Type)
  = Free (Var a var)
  | Ground (Reified a var)

--------------------------------------------------------------------------------
-- Higher-rank Type Aliases
--------------------------------------------------------------------------------

-- | A unification function for any LogicType.
type Unifier rel var =
  forall t. LogicType t => Logic t var -> Logic t var -> rel ()

-- | An evaluation function for any LogicType.
type Evaluator rel var =
  forall t. LogicType t => Logic t var -> rel t

--------------------------------------------------------------------------------
-- Child Traversal
--------------------------------------------------------------------------------

-- | A child field inside a reified value.
--
-- Existential wrapper for uniform traversal of heterogeneous children.
-- Only requires 'LogicRepr', enabling use in typesetting without 'LogicType'.
data Field parent var where
  Field :: (LogicRepr t, Typeable t) => Proxy t -> Logic t var -> Field parent var

--------------------------------------------------------------------------------
-- LogicRepr Class (Minimal)
--------------------------------------------------------------------------------

-- | Minimal class for types that have a logic representation.
--
-- Use this as the constraint when you only need the type structure
-- (e.g., for AST construction with 'fresh', or typesetting).
class Typeable a => LogicRepr a where
  -- | Reified representation of @a@ that stores children as 'Logic' terms.
  data Reified a (var :: Type -> Type) :: Type

  -- | Embed a ground Haskell value into its reified representation.
  project :: a -> Reified a var

  -- | Attempt to extract a fully ground Haskell value.
  reify :: Reified a var -> Maybe a

  -- | Quote a reified value: constructor name and children.
  --
  -- This is the structural representation used for traversal and display.
  quote :: Reified a var -> (String, [Field a var])

  -- | Effectful display of a reified value.
  --
  -- Takes a continuation for rendering child 'Logic' terms.
  -- The 'Applicative' allows threading effects (e.g., State for renumbering).
  --
  -- Default implementation uses 'quote' to produce @Con(child1, child2, ...)@.
  display :: Applicative f
          => (forall t. LogicRepr t => Logic t var -> f String)
          -> Reified a var
          -> f String
  display render r = case quote r of
    (name, []) -> pure name
    (name, cs) ->
      (\strs -> name ++ "(" ++ intercalate ", " strs ++ ")")
        <$> traverse (\(Field _ l) -> render l) cs

-- | Intercalate for strings (local helper).
intercalate :: String -> [String] -> String
intercalate _ []     = ""
intercalate _ [x]    = x
intercalate sep (x:xs) = x ++ sep ++ intercalate sep xs

--------------------------------------------------------------------------------
-- LogicType Class (Full)
--------------------------------------------------------------------------------

-- | Full class for types that can participate in logic programming.
--
-- Extends 'LogicRepr' with methods for unification and evaluation.
-- Use 'snd . quote' to get children for traversal (e.g., occurs check).
class LogicRepr a => LogicType a where
  -- | Unify two reified values.
  unifyVal :: Alternative rel => Unifier rel var -> Reified a var -> Reified a var -> rel ()

  -- | Fully dereference a reified value.
  derefVal :: Alternative rel => Evaluator rel var -> Reified a var -> rel a

--------------------------------------------------------------------------------
-- Core Types for Interpreters
--------------------------------------------------------------------------------

-- | A logic goal (relation body).
type Goal rel = rel ()

-- | How to allocate a fresh variable.
data FreshType (rel :: Type -> Type) (t :: Type) where
  FreshVar :: FreshType rel t
  ArgVar   :: (Redex rel, LogicType t) => Logic t (RVar rel) -> FreshType rel t

--------------------------------------------------------------------------------
-- Redex: Core Interpreter Class
--------------------------------------------------------------------------------

-- | Core typeclass for logic programming interpreters.
class (Monad rel, Alternative rel, Functor (RVar rel)) => Redex rel where
  -- | Type family for logic variables.
  data RVar rel :: Type -> Type

  -- | Allocate a fresh variable (CPS style).
  fresh_ :: LogicRepr t => FreshType rel t -> (Var t (RVar rel) -> rel a) -> rel a

  -- | Unify two logic terms.
  unify :: LogicType a => Logic a (RVar rel) -> Logic a (RVar rel) -> Goal rel

  -- | Display a variable as a string (for debugging).
  displayVar :: RVar rel t -> String

  -- | Insert a suspension point for fair interleaving.
  suspend :: rel a -> rel a

