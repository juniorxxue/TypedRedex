{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}

-- | Stratified typeclasses for TypedRedex interpreters.
--
-- = Typeclass Hierarchy
--
-- @
-- Redex rel                    -- Core: fresh_, unify, suspend
--   │
--   ├── RedexEval rel          -- Evaluation: derefVar
--   │
--   ├── RedexNeg rel           -- Negation: neg
--   │
--   └── RedexStructure rel     -- Structure: onRuleEnter, onRuleExit
-- @
--
-- = Implementing Interpreters
--
-- **Minimal (eval only)**: Implement 'Redex' + 'RedexEval'
--
-- **With negation**: Also implement 'RedexNeg'
--
-- **With derivations**: Also implement 'RedexStructure'
module TypedRedex.Logic.Redex
  ( -- * Core Types
    Goal
  , Relation(..)
  , CapturedTerm(..)
  , FreshType(..)
  , CallType(..)
    -- * Typeclass Hierarchy
  , Redex(..)
  , RedexEval(..)
  , RedexNeg(..)
  , RedexStructure(..)
  , RedexFresh(..)
  , RedexHash(..)
    -- * Variable Equality
  , EqVar(..)
    -- * Re-exports
  , Alternative(empty, (<|>))
  ) where

import Data.Kind (Type)
import Data.Typeable (Typeable)
import Control.Applicative (Alternative(empty, (<|>)))
import TypedRedex.Logic.Term
import TypedRedex.Logic.Nominal (NominalAtom, Hash)

--------------------------------------------------------------------------------
-- Core Types
--------------------------------------------------------------------------------

-- | A logic goal (relation body).
--
-- Goals live in the interpreter monad and signal success/failure via
-- 'Alternative'.
type Goal rel = rel ()

-- | A captured logic term for deferred resolution.
--
-- This existential type allows storing logic terms of different types,
-- resolved to strings at render time after unification completes.
data CapturedTerm (rel :: Type -> Type) where
  CapturedTerm :: (LogicType a, Typeable a) => Logic a (RVar rel) -> CapturedTerm rel

-- | A named logic relation (predicate).
data Relation (rel :: Type -> Type) = Relation
  { relName  :: String              -- ^ Relation name
  , relTerms :: [CapturedTerm rel]  -- ^ Captured terms
  , relBody  :: Goal rel            -- ^ The computation
  }

-- | How to allocate a fresh variable.
data FreshType (rel :: Type -> Type) (t :: Type) where
  FreshVar :: FreshType rel t
  ArgVar   :: (Redex rel, LogicType t) => Logic t (RVar rel) -> FreshType rel t

-- | How to invoke a relation.
data CallType = Opaque | Transparent
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Redex: Core Typeclass
--------------------------------------------------------------------------------

-- | Core typeclass for logic programming.
--
-- Every interpreter must implement this. Provides:
--
-- * Variable allocation ('fresh_')
-- * Unification ('unify')
-- * Fair interleaving ('suspend')
class (Monad rel, Alternative rel, Functor (RVar rel)) => Redex rel where

  -- | Type family for logic variables.
  data RVar rel :: Type -> Type

  -- | Allocate a fresh variable (CPS style).
  fresh_ :: (LogicType t) => FreshType rel t -> (Var t (RVar rel) -> rel a) -> rel a

  -- | Unify two logic terms.
  unify :: (LogicType a) => Logic a (RVar rel) -> Logic a (RVar rel) -> Goal rel

  -- | Display a variable as a string (for debugging).
  displayVar :: RVar rel t -> String

  -- | Insert a suspension point for fair interleaving.
  suspend :: rel a -> rel a

  -- | Invoke a relation with suspension control.
  call_ :: CallType -> Relation rel -> Goal rel
  call_ Opaque rel = suspend (relBody rel)
  call_ Transparent rel = relBody rel

  ---------------------------------------------------------------------------
  -- Interpretation markers (no-op by default)
  ---------------------------------------------------------------------------

  -- | Mark the start of a conclusion pattern.
  markConclusion :: Goal rel
  markConclusion = pure ()

  -- | Mark a premise call.
  markPremise :: String -> [CapturedTerm rel] -> Goal rel
  markPremise _ _ = pure ()

  -- | Whether to skip lifted (deferred) actions.
  skipLiftedActions :: proxy rel -> Bool
  skipLiftedActions _ = False

--------------------------------------------------------------------------------
-- RedexEval: Evaluation
--------------------------------------------------------------------------------

-- | Extract ground values from logic terms.
class (Redex rel) => RedexEval rel where
  -- | Fully dereference a variable to a ground value.
  derefVar :: (LogicType a) => Var a (RVar rel) -> rel a

--------------------------------------------------------------------------------
-- RedexNeg: Negation
--------------------------------------------------------------------------------

-- | Negation-as-failure for logic programming.
class (Redex rel) => RedexNeg rel where
  -- | Succeed if a goal has no solutions.
  neg :: Goal rel -> Goal rel

--------------------------------------------------------------------------------
-- RedexStructure: Derivation Tracking
--------------------------------------------------------------------------------

-- | Structure tracking for derivation trees.
class (Redex rel) => RedexStructure rel where
  -- | Called when entering a rule body.
  onRuleEnter :: String -> [String] -> Goal rel

  -- | Called when exiting a rule body.
  onRuleExit :: String -> Goal rel

  -- | Wrap a premise call for tracking.
  withPremise :: String -> [String] -> rel a -> rel a
  withPremise _ _ = id

--------------------------------------------------------------------------------
-- RedexFresh: Fresh Name Generation
--------------------------------------------------------------------------------

-- | Fresh name generation for nominal logic.
--
-- Interpreters that support nominal atoms (name binding) implement this
-- to provide unique integers for generating fresh names.
class Redex rel => RedexFresh rel where
  -- | Generate a fresh unique integer.
  --
  -- Users build their own nominal atom generators using this:
  --
  -- @
  -- freshNom :: RedexFresh rel => rel Nom
  -- freshNom = Nom \<$\> freshInt
  -- @
  freshInt :: rel Int

--------------------------------------------------------------------------------
-- RedexHash: Hash Constraints (Freshness)
--------------------------------------------------------------------------------

-- | Hash (freshness) constraint support for nominal logic.
--
-- The hash constraint @a # t@ asserts that name @a@ does not occur free
-- in term @t@. This is essential for capture-avoiding substitution.
class Redex rel => RedexHash rel where
  -- | Assert a hash (freshness) constraint: @name # term@.
  --
  -- This succeeds immediately if both arguments are ground and the
  -- constraint is satisfied, or stores the constraint for later checking
  -- if either argument contains unbound variables.
  hash :: (NominalAtom name, LogicType name, LogicType term, Hash name term)
       => Logic name (RVar rel) -> Logic term (RVar rel) -> Goal rel

--------------------------------------------------------------------------------
-- Variable Equality
--------------------------------------------------------------------------------

-- | Equality comparison for logic variables (for occurs check).
class EqVar rel where
  varEq :: (RVar rel) a -> (RVar rel) b -> Bool
