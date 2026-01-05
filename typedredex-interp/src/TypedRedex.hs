-- | TypedRedex: Main public API
--
-- This module provides the user-facing API for writing logic programs.
-- TypedRedex is a shallow embedding of PLT Redex in Haskell with a
-- Kanren-like solver, enabling direct use of Haskell's control flow,
-- pattern matching, and modularity.
--
-- = Quick Start
--
-- Import this module to get everything you need:
--
-- @
-- import TypedRedex
-- @

module TypedRedex
  (
    -- * Core types
    Relation(..)          -- ^ Named logic relations with name, terms, and body
  , CapturedTerm(..)      -- ^ Existentially wrapped logic terms for deferred resolution
  , Goal                  -- ^ Type alias for relation goals: rel ()
  , Redex(RVar)           -- ^ Typeclass for logic programming monads
  , RedexEval             -- ^ Extract ground values from logic terms
  , RedexNeg              -- ^ Negation support
  , LogicType(..)         -- ^ Types that can be used in logic programs
  , Logic(..)             -- ^ Logic terms: Free (variable) or Ground (value)
  , LTerm                 -- ^ Type alias for Logic a (RVar rel)
  , LVar                  -- ^ Type alias for Var a (RVar rel)

    -- * Creating fresh variables
    -- | Allocate unbound logic variables or nominal atoms (exists quantification).
    -- The type of each variable is inferred from usage context.
  , Freshable(..)
  , fresh, fresh2, fresh3, fresh4, fresh5, fresh6, fresh7

    -- * Defining relations
    -- | Build named relations from Haskell functions
  , relation, relation2, relation3, relation4, relation5

    -- * Invoking relations
  , call       -- ^ Invoke a relation with fair interleaving
  , callDirect -- ^ Invoke a relation without suspension (direct execution)

    -- * Evaluation
  , eval   -- ^ Extract ground value from a logic term

    -- * Running moded judgments
    -- | Run moded judgments with lambda-captured outputs
  , inject   -- ^ Convert ground Haskell value to moded term
  , goal     -- ^ Extract goal from judgment application
  , run, run2, run3, run4, run5

    -- * Unification
  , (<=>)  -- ^ Unify two logic terms

    -- * Disjunction
  , conde  -- ^ Disjunction: try multiple goal clauses

    -- * Negation
  , neg    -- ^ Constructive negation: succeed if goal has no solutions

    -- * Moded DSL (compile-time mode checking)
  , Mode(..)
  , ModeList(..)
  , T(..)
  , TArgs(..)
  , AppliedM(..)
  , Judgment1
  , Judgment2
  , Judgment3
  , mjudge
  , mjudge1, mjudge2, mjudge3
  , toApplied
  , ToLTermList(..)
  , ModedRule(..)
  , ruleM
  , CheckSchedule
  , ground
  , lift1, lift2, lift3
  , Union

    -- * Core types from Define (for interpreter compatibility)
  , Applied(..)
  , LTermList(..)
  ) where

-- Core types (from typedredex-logic)
import TypedRedex.Logic (Redex(..), RedexEval(..), RedexNeg(..), RedexStructure(..), Relation(..), CapturedTerm(..), Goal, EqVar(..), neg)
import TypedRedex.Logic (Logic(..), LogicType(..), Var, Field(..))

-- DSL: Fresh variables and type aliases (from typedredex-dsl)
import TypedRedex.DSL.Fresh (LTerm, LVar, Freshable(..), fresh, fresh2, fresh3, fresh4, fresh5, fresh6, fresh7, argument, argument2, argument3, argument4, argument5)

-- DSL: Moded (compile-time mode checking)
import TypedRedex.DSL.Moded (Mode(..), ModeList(..), T(..), TArgs(..), AppliedM(..), Judgment1, Judgment2, Judgment3, mjudge, mjudge1, mjudge2, mjudge3, toApplied, ToLTermList(..), ModedRule(..), ruleM, CheckSchedule, ground, lift1, lift2, lift3, Union)

-- DSL: Core types (for interpreter compatibility)
import TypedRedex.DSL.Define (Applied(..), LTermList(..))

-- Relation primitives (from typedredex-dsl)
import TypedRedex.DSL.Relation (relation, relation2, relation3, relation4, relation5, call, callDirect, (<=>), conde)

-- Evaluation and running (from typedredex-interp)
import TypedRedex.Interp.Run
  ( eval, run, run2, run3, run4, run5
  , inject, goal
  )
