{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

-- | Core logic term representation and the 'LogicType' class.
--
-- This module defines the minimal data model for TypedRedex:
--
-- * 'Logic' – either a free logic variable ('Free') or a ground value ('Ground')
-- * 'Var' – a typed logic variable
-- * 'LogicType' – types that can participate in logic programming
-- * 'Field' – existential wrapper for traversing children
--
-- This is the pure core with no presentation concerns (no TypesetNaming, no quote).
module TypedRedex.Logic.Term
  ( -- * Logic terms
    Logic(..)
  , Var(..)
    -- * Logic types
  , LogicType(..)
    -- * Higher-rank helpers
  , Unifier
  , Evaluator
    -- * Child traversal
  , Field(..)
  ) where

import Control.Applicative (Alternative)
import Data.Kind (Type)
import Data.Proxy (Proxy)
import Data.Typeable (Typeable)
import TypedRedex.Logic.Display (HasDisplay)

--------------------------------------------------------------------------------
-- Logic terms and variables
--------------------------------------------------------------------------------

-- | A typed logic variable for values of type @a@.
--
-- Each interpreter chooses a type constructor @var :: Type -> Type@ for
-- variable representation. A 'Var a var' points to a cell that eventually
-- contains a @Logic a var@.
newtype Var (a :: Type) (var :: Type -> Type) = Var
  { unVar :: var (Logic a var)
  }

-- | A logic term: either a free variable or a ground value.
--
-- @
-- Free v      -- Unbound logic variable
-- Ground r    -- Reified ground value (may contain Free children)
-- @
data Logic (a :: Type) (var :: Type -> Type)
  = Free (Var a var)
  | Ground (Reified a var)

--------------------------------------------------------------------------------
-- Higher-rank type aliases
--------------------------------------------------------------------------------

-- | A unification function for any LogicType.
type Unifier rel var =
  forall t. LogicType t => Logic t var -> Logic t var -> rel ()

-- | An evaluation function for any LogicType.
type Evaluator rel var =
  forall t. LogicType t => Logic t var -> rel t

--------------------------------------------------------------------------------
-- Child traversal
--------------------------------------------------------------------------------

-- | A child field inside a reified value.
--
-- This existential wrapper allows uniform traversal of heterogeneous children
-- (e.g., for occurs check). The 'Proxy' carries the child's type.
-- The 'HasDisplay' constraint enables recursive pretty-printing.
data Field parent var where
  Field :: (LogicType t, Typeable t, HasDisplay t) => Proxy t -> Logic t var -> Field parent var

--------------------------------------------------------------------------------
-- LogicType class
--------------------------------------------------------------------------------

-- | Types that can be used as logic terms.
--
-- Instances define an associated 'Reified' representation which contains
-- 'Logic' children instead of plain Haskell values. This enables:
--
-- * Structural unification ('unifyVal')
-- * Evaluation/dereferencing ('derefVal')
-- * Child traversal ('children')
-- * Pretty-printing ('quote') - optional, for presentation layer
--
-- Note: The 'quote' method is optional and primarily used by the interpreter
-- layer for pretty-printing. Core functionality only requires 'children'.
class Typeable a => LogicType a where
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

  -- | Fully dereference a reified value, given an evaluator for child terms.
  derefVal :: Alternative rel => Evaluator rel var -> Reified a var -> rel a

  -- | Get all logic children for traversal (used by occurs check).
  --
  -- Returns a list of existentially-wrapped child terms.
  children :: Reified a var -> [Field a var]

  -- | Quote a reified value for pretty-printing.
  --
  -- Returns the constructor name and its fields. Default implementation
  -- returns a placeholder - override for actual pretty-printing support.
  quote :: Reified a var -> (String, [Field a var])
  quote r = ("?", children r)
