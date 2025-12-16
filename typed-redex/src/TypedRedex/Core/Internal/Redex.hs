{-# LANGUAGE GADTs, KindSignatures, FlexibleContexts, TypeFamilies #-}

-- | Internal.Redex: Stratified typeclasses for TypedRedex interpreters
--
-- = Architecture Overview
--
-- @
-- ┌─────────────────────────────────────────────────────────────┐
-- │  User Code (examples/pcf-step, examples/stlc-bidir)        │
-- ├─────────────────────────────────────────────────────────────┤
-- │  Utils Layer (Utils/Redex.hs, Utils/Rule.hs)               │
-- ├─────────────────────────────────────────────────────────────┤
-- │  THIS MODULE: Stratified Typeclasses                       │
-- │                                                            │
-- │    Redex           ← Core: variables, unification          │
-- │      ↓                                                     │
-- │    RedexEval       ← Extract ground values                 │
-- │      ↓                                                     │
-- │    RedexNeg        ← Disequality and negation              │
-- │      ↓                                                     │
-- │    RedexStructure  ← Derivation tree tracking              │
-- │                                                            │
-- ├─────────────────────────────────────────────────────────────┤
-- │  Interpreters (SubstRedex, TracingRedex)                   │
-- └─────────────────────────────────────────────────────────────┘
-- @
--
-- = Typeclass Hierarchy
--
-- @
-- Redex rel                    -- Core: fresh_, unify, suspend
--   │
--   ├── RedexEval rel          -- Evaluation: derefVar
--   │
--   ├── RedexNeg rel           -- Negation: diseq, neg
--   │
--   └── RedexStructure rel     -- Structure: onRuleEnter, onRuleExit
-- @
--
-- = Implementing Interpreters
--
-- **Minimal (eval only)**: Implement 'Redex' + 'RedexEval'
--
-- @
-- instance Redex MyInterp where
--   data RVar MyInterp t = ...
--   fresh_ = ...
--   unify = ...
--   displayVar = ...
--   suspend = ...
--
-- instance RedexEval MyInterp where
--   derefVar = ...
-- @
--
-- **With negation**: Also implement 'RedexNeg'
--
-- @
-- instance RedexNeg MyInterp where
--   diseq = ...
--   neg = ...
-- @
--
-- **With derivations**: Also implement 'RedexStructure'
--
-- @
-- instance RedexStructure MyInterp where
--   onRuleEnter name args = pushFrame name args
--   onRuleExit name = popFrame
-- @

module TypedRedex.Core.Internal.Redex
  ( -- * Core Types
    Relation(..)
  , FreshType(..)
  , CallType(..)
    -- * Typeclass Hierarchy
  , Redex(..)
  , RedexEval(..)
  , RedexNeg(..)
  , RedexStructure(..)
    -- * Variable Equality
  , EqVar(..)
    -- * Re-exports
  , Alternative(empty, (<|>))
  ) where

import Data.Kind (Type)
import Control.Applicative (Alternative(empty, (<|>)))
import TypedRedex.Core.Internal.Logic

--------------------------------------------------------------------------------
-- Core Types
--------------------------------------------------------------------------------

-- | A named logic relation (predicate).
--
-- @
-- Relation "append" ["xs", "ys", "zs"] bodyComputation
-- @
--
-- The name and args are used for debugging and derivation trees.
-- The body returns @()@; success/failure is via 'Alternative'.
data Relation (rel :: Type -> Type) = Relation
  { relName :: String      -- ^ Relation name (e.g., "step", "value")
  , relArgs :: [String]    -- ^ Pretty-printed arguments
  , relBody :: rel ()      -- ^ The computation
  }

-- | How to allocate a fresh variable.
--
-- @
-- FreshVar         -- Unbound (for ∃ quantification)
-- ArgVar term      -- Pre-bound (for embedding ground values)
-- @
data FreshType (rel :: Type -> Type) (t :: Type) where
  FreshVar :: FreshType rel t
  ArgVar   :: (Redex rel, LogicType t) => Logic t (RVar rel) -> FreshType rel t

-- | How to invoke a relation.
--
-- @
-- Opaque      -- With suspension (fair interleaving)
-- Transparent -- Direct execution (no suspension)
-- @
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
--
-- == Superclasses
--
-- * 'Monad': Conjunction via @>>=@
-- * 'Alternative': Disjunction via @\<|>@, failure via @empty@
--
-- == Minimal Implementation
--
-- @
-- instance Redex MyInterp where
--   data RVar MyInterp t = MyVar Int
--   fresh_ FreshVar k   = allocFreshVar >>= k
--   fresh_ (ArgVar x) k = allocBoundVar x >>= k
--   unify = myUnify
--   displayVar (MyVar n) = "x" ++ show n
--   suspend = mySuspend  -- or 'id' if no interleaving
-- @
class (Monad rel, Alternative rel, Functor (RVar rel)) => Redex rel where

  -- | Type family for logic variables.
  --
  -- Each interpreter chooses its representation:
  --
  -- @
  -- data RVar SubstRedex t = SVar Int      -- Integer-based
  -- data RVar NamedInterp t = NVar String  -- Name-based
  -- @
  data RVar rel :: Type -> Type

  -- | Allocate a fresh variable.
  --
  -- Uses CPS to prevent variable escape (like ST monad).
  --
  -- @
  -- fresh_ FreshVar $ \\x -> ...      -- Unbound variable
  -- fresh_ (ArgVar term) $ \\x -> ... -- Pre-bound variable
  -- @
  fresh_ :: (LogicType t) => FreshType rel t -> (Var t (RVar rel) -> rel a) -> rel a

  -- | Unify two logic terms.
  --
  -- Core operation of logic programming (Prolog's @=@).
  --
  -- * @Free x@ with @y@: bind @x@ to @y@
  -- * @Ground a@ with @Ground b@: recursively unify
  -- * Different constructors: fail (@empty@)
  -- * Occurs check failure: fail
  unify :: (LogicType a) => Logic a (RVar rel) -> Logic a (RVar rel) -> rel ()

  -- | Display a variable as a string.
  --
  -- For debugging and derivation pretty-printing.
  displayVar :: RVar rel t -> String

  -- | Insert a suspension point for fair interleaving.
  --
  -- This is the key to fair search: allows scheduler to switch branches.
  --
  -- @
  -- -- SubstRedex: wrap in Immature thunk
  -- suspend m = SubstRedex $ mapStateT Immature $ runSubstRedex m
  --
  -- -- No interleaving: just identity
  -- suspend = id
  -- @
  suspend :: rel a -> rel a

  -- | Invoke a relation with suspension control.
  --
  -- Default implementation:
  --
  -- @
  -- call_ Opaque rel      = suspend (runRelation rel)
  -- call_ Transparent rel = runRelation rel
  -- @
  --
  -- Interpreters that track structure (like TracingRedex) should override
  -- this to call 'onRuleEnter'/'onRuleExit' from 'RedexStructure'.
  call_ :: CallType -> Relation rel -> rel ()
  call_ Opaque rel = suspend (relBody rel)
  call_ Transparent rel = relBody rel

--------------------------------------------------------------------------------
-- RedexEval: Evaluation
--------------------------------------------------------------------------------

-- | Extract ground values from logic terms.
--
-- Separate from 'Redex' because:
--
-- * Not all interpreters evaluate (e.g., constraint collectors, deep extractors)
-- * Evaluation requires variables to be bound
--
-- == Example
--
-- @
-- runSubstRedex $ fresh $ \\x -> do
--   x \<=> zero
--   derefVar x    -- Returns: Zero
-- @
class (Redex rel) => RedexEval rel where

  -- | Fully dereference a variable to a ground value.
  --
  -- Follows substitution chain: @x → y → z → Ground value@
  --
  -- Fails if variable remains unbound after solving.
  derefVar :: (LogicType a) => Var a (RVar rel) -> rel a

--------------------------------------------------------------------------------
-- RedexNeg: Negation
--------------------------------------------------------------------------------

-- | Negation-as-failure for logic programming.
--
-- Interpreters that support negation implement this.
-- This extends core miniKanren with the ability to succeed when a goal fails.
--
-- == Example
--
-- @
-- -- Succeed only if (x = zero) has no solutions
-- neg (x \<=> zero)
-- @
--
-- == Implementation Notes
--
-- Negation-as-failure runs the goal and succeeds if it produces no answers.
-- This is sound for ground goals but may not terminate for goals with
-- infinite answer streams.
class (Redex rel) => RedexNeg rel where

  -- | Negation-as-failure: succeed if a goal has no solutions.
  --
  -- @neg g@ succeeds if @g@ produces no answers under the current
  -- substitution, and fails if @g@ has at least one answer.
  --
  -- WARNING: This will not terminate if @g@ diverges before producing
  -- its first answer. Use with care on potentially infinite computations.
  neg :: rel () -> rel ()

--------------------------------------------------------------------------------
-- RedexStructure: Derivation Tracking
--------------------------------------------------------------------------------

-- | Structure tracking for derivation trees.
--
-- Interpreters that build proof trees implement this.
-- Simple eval interpreters can skip this entirely.
--
-- == Derivation Stack Model
--
-- @
-- 1. onRuleEnter "β" args  → push frame onto stack
-- 2. (premises execute, adding children)
-- 3. onRuleExit "β"        → pop frame, build Derivation node
-- @
--
-- == Example Implementation (TracingRedex)
--
-- @
-- instance RedexStructure TracingRedex where
--   onRuleEnter name args = modify $ pushFrame name args
--   onRuleExit _ = modify popFrame
--   withPremise _ _ body = body  -- premises tracked via call_
-- @
class (Redex rel) => RedexStructure rel where

  -- | Called when entering a rule body.
  --
  -- Typically: push a new derivation frame onto the stack.
  --
  -- @
  -- onRuleEnter "⇒App" ["Γ", "e1 e2", "B"]
  -- @
  onRuleEnter :: String -> [String] -> rel ()

  -- | Called when exiting a rule body.
  --
  -- Typically: pop frame, create Derivation node, attach to parent.
  --
  -- @
  -- onRuleExit "⇒App"
  -- @
  onRuleExit :: String -> rel ()

  -- | Wrap a premise call for tracking.
  --
  -- Allows recording which sub-goals are called as premises.
  --
  -- Default: just run the body.
  --
  -- @
  -- withPremise "value" ["v"] $ call (value v)
  -- @
  withPremise :: String -> [String] -> rel a -> rel a
  withPremise _ _ = id

--------------------------------------------------------------------------------
-- Variable Equality
--------------------------------------------------------------------------------

-- | Equality comparison for logic variables.
--
-- Needed for:
--
-- * Occurs check: Does @x@ appear in term @t@?
-- * Substitution lookup
--
-- Compares variable /identity/, not values.
class EqVar rel where
  varEq :: (RVar rel) a -> (RVar rel) b -> Bool
