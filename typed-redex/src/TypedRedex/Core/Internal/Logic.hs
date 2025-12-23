{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

-- | Core logic term representation and the 'LogicType' class.
--
-- This module defines the minimal data model that all TypedRedex interpreters
-- operate on:
--
-- * 'Logic' – either a free logic variable ('Free') or a fully reified value
--   ('Ground').
-- * 'Var'   – a typed logic variable, abstract over the interpreter's chosen
--   representation.
-- * 'LogicType' – user-defined datatypes that can participate in unification
--   and evaluation.
--
-- Users rarely interact with this module directly; the recommended entrypoint
-- for writing relations is "TypedRedex". However, when defining custom syntax
-- types (or deriving instances), these types show up in error messages and
-- editor hover info — so we keep the signatures and names intentionally
-- “print-friendly”.
module TypedRedex.Core.Internal.Logic
  ( -- * Logic terms
    Logic(..)
  , Var(..)
    -- * Unification/evaluation helpers (higher-rank)
  , Unifier
  , Evaluator
    -- * Generic field wrapper (for pretty-printing)
  , Field(..)
    -- * Logic types
  , LogicType(..)
  ) where

import Control.Applicative (Alternative)
import Data.Kind (Type)
import Data.Proxy (Proxy)
import TypedRedex.Interp.PrettyPrint (LogicVarNaming)

--------------------------------------------------------------------------------
-- Logic terms and variables
--------------------------------------------------------------------------------

-- | A typed logic variable for values of type @a@.
--
-- Internally, each interpreter picks a type constructor @var :: Type -> Type@
-- for variable identities; a 'Var a var' is a @var@ pointing at a cell that
-- eventually contains a @Logic a var@.
newtype Var (a :: Type) (var :: Type -> Type) = Var
  { unVar :: var (Logic a var)
  }

-- | A logic term: either a free variable or a fully reified value.
data Logic (a :: Type) (var :: Type -> Type)
  = Free (Var a var)
  | Ground (Reified a var)

-- | A unification function that can unify logic terms of /any/ 'LogicType'.
type Unifier rel var =
  forall t. LogicType t => Logic t var -> Logic t var -> rel ()

-- | An evaluation function that can fully dereference logic terms of /any/
-- 'LogicType'.
type Evaluator rel var =
  forall t. LogicType t => Logic t var -> rel t

--------------------------------------------------------------------------------
-- Generic constructor view (for pretty-printing)
--------------------------------------------------------------------------------

-- | A field inside a reified value.
--
-- This existential wrapper allows us to treat different field types uniformly
-- when traversing a value's structure for pretty-printing.
data Field parent var where
  Field :: LogicType t => Proxy t -> Logic t var -> Field parent var

--------------------------------------------------------------------------------
-- LogicType
--------------------------------------------------------------------------------

-- | Types that can be used as logic terms.
--
-- Instances define an associated 'Reified' representation which contains
-- 'Logic' children instead of plain Haskell values. This enables:
--
-- * Structural unification ('unifyVal')
-- * Quoting for pretty-printing ('quote')
-- * Evaluation/dereferencing ('derefVal')
class LogicVarNaming a => LogicType a where
  -- | Reified representation of @a@ that stores children as 'Logic' terms.
  data Reified a (var :: Type -> Type) :: Type

  -- | Embed a ground Haskell value into its reified representation.
  project :: a -> Reified a var

  -- | Attempt to extract a fully ground Haskell value.
  --
  -- Returns 'Nothing' if the value still contains variables.
  reify :: Reified a var -> Maybe a

  -- | Unify two reified values, given a unifier for child 'Logic' terms.
  unifyVal :: Alternative rel => Unifier rel var -> Reified a var -> Reified a var -> rel ()

  -- | View a reified value as a constructor name + list of fields (for pretty-printing).
  quote :: Reified a var -> (String, [Field a var])

  -- | Fully dereference a reified value, given an evaluator for child terms.
  derefVal :: Alternative rel => Evaluator rel var -> Reified a var -> rel a
