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
--
-- = Key Concepts
--
-- 1. **Relations** (Relation rel): Logic predicates that can succeed with multiple solutions
--    - Think of them as non-deterministic boolean functions
--    - Can be called, unified, and composed
--
-- 2. **Logic variables** (RVar): Unification variables (like Prolog variables)
--    - Created with fresh, fresh2, etc.
--    - Bound through unification (<=>)
--
-- 3. **Logic terms** (LTerm a rel): Either ground values (Ground) or variables (Free)
--    - LTerm Nat rel: a natural number that might be a variable
--    - LTerm (Tm, Ty) rel: a pair where components might be variables
--
-- 4. **Unification** (<=>): Equate two logic terms
--    - Can bind variables, fail if incompatible, or recursively unify structures
--
-- 5. **Disjunction** (conde, <|>): Try multiple alternatives (OR)
--    - Produces a stream of solutions
--
-- 6. **Conjunction** (>>, do-notation): Sequence goals (AND)
--    - All goals must succeed
--
-- 7. **Interpreters**: Different ways to run relations
--    - SubstRedex: substitution-based with interleaving
--    - TracingRedex: tracks derivation trees for proof output
--    - TypesettingRedex: builds AST for rule extraction

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
    -- | Allocate unbound logic variables or nominal atoms (∃ quantification).
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

    -- * Running logic programs
    -- | Execute relations and return streams of solutions
  , run, run2, run3, run4, run5

    -- * Unification
  , (<=>)  -- ^ Unify two logic terms

    -- * Disjunction
  , conde  -- ^ Disjunction: try multiple goal clauses

    -- * Negation
  , neg    -- ^ Constructive negation: succeed if goal has no solutions

    -- * Moded DSL (compile-time mode checking)
    -- | The moded DSL provides compile-time verification that all rules
    -- have valid execution schedules. Use qualified import:
    -- @import qualified TypedRedex.DSL.Moded as R@
    --
    -- Key combinators:
    -- - @fresh@: Create tracked logic variables
    -- - @concl@: Specify rule conclusion
    -- - @prem@: Add rule premises
    -- - @liftRel@: Lift rel actions into RuleM
    -- - @mjudge1@, @mjudge2@, @mjudge3@: Define mode-checked judgments
    -- - @ruleM@: Define mode-checked rules
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

-- Core types
import TypedRedex.Core.Internal.Redex (Redex(..), RedexEval(..), RedexNeg(..), RedexStructure(..), Relation(..), CapturedTerm(..), Goal, EqVar(..))
import TypedRedex.Core.Internal.Logic (Logic(..), LogicType(..), Var, Reified, Field(..))

-- DSL: Fresh variables and type aliases
import TypedRedex.DSL.Fresh (LTerm, LVar, Freshable(..), fresh, fresh2, fresh3, fresh4, fresh5, fresh6, fresh7, argument, argument2, argument3, argument4, argument5)

-- DSL: Moded (compile-time mode checking)
import TypedRedex.DSL.Moded (Mode(..), ModeList(..), T(..), TArgs(..), AppliedM(..), Judgment1, Judgment2, Judgment3, mjudge, mjudge1, mjudge2, mjudge3, toApplied, ToLTermList(..), ModedRule(..), ruleM, CheckSchedule, ground, lift1, lift2, lift3, Union)

-- DSL: Core types (for interpreter compatibility)
import TypedRedex.DSL.Define (Applied(..), LTermList(..))

-- Relation primitives
import TypedRedex.Core.Internal.Relation (relation, relation2, relation3, relation4, relation5, call, callDirect, (<=>), conde)

-- Evaluation and running
import TypedRedex.Interp.Run (eval, run, run2, run3, run4, run5)

-- Negation (from Core)
import TypedRedex.Core.Internal.Redex (neg)
