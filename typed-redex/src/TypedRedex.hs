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
--    - Bound through unification (===)
--
-- 3. **Logic terms** (L a rel): Either ground values (Ground) or variables (Free)
--    - L Nat rel: a natural number that might be a variable
--    - L (Tm, Ty) rel: a pair where components might be variables
--
-- 4. **Unification** (===, <=>): Equate two logic terms
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
--    - DeepRedex: builds AST for rule extraction

module TypedRedex
  (
    -- * Core types
    Relation(..)          -- ^ Named logic relations with name, terms, and body
  , CapturedTerm(..)      -- ^ Existentially wrapped logic terms for deferred resolution
  , Redex(RVar)           -- ^ Typeclass for logic programming monads
  , RedexEval             -- ^ Extract ground values from logic terms
  , RedexNeg              -- ^ Negation support
  , LogicType             -- ^ Types that can be used in logic programs
  , Logic(..)             -- ^ Logic terms: Free (variable) or Ground (value)
  , L                     -- ^ Type alias for Logic a (RVar rel)

    -- * Creating fresh variables
    -- | Allocate unbound logic variables (∃ quantification)
  , fresh, fresh2, fresh3, fresh4, fresh5

    -- * Defining relations
    -- | Build named relations from Haskell functions
  , relation, relation2, relation3, relation4, relation5

    -- * Defining inference rules (for derivation tracking)
    -- | Build relations in rule style with conclusion patterns
  , rule, rule1, rule2, rule3, rule4, rule5

    -- * Invoking relations
  , call   -- ^ Invoke a relation (goal call)
  , premise -- ^ Alias for call
  , embed  -- ^ Embed a relation transparently

    -- * Evaluation
  , eval   -- ^ Extract ground value from a logic term

    -- * Running logic programs
    -- | Execute relations and return streams of solutions
  , run, run2, run3, run4, run5

    -- * Unification and relational operators
  , (===)  -- ^ Unify logic term with ground pattern
  , (<=>)  -- ^ Unify two logic terms

    -- * Disjunction
  , conde  -- ^ Disjunction: try multiple goal clauses

    -- * Negation
  , neg    -- ^ Constructive negation: succeed if goal has no solutions

    -- * Clean DSL syntax (judgment/rule/concl/prem)
  , Applied(..), Applied2(..), Applied3(..), Applied4(..), Applied5(..)
  , Conclude(..)  -- concl method + ConcludePat type family
  , Premise(..)   -- prem method
  , Rule(..), Rule2(..), Rule3(..), Rule4(..), Rule5(..)
  , judgment, judgment2, judgment3, judgment4, judgment5
  ) where

-- Core types
import TypedRedex.Core.Internal.Redex (Redex(..), RedexEval(..), RedexNeg(..), RedexStructure(..), Relation(..), CapturedTerm(..), EqVar(..))
import TypedRedex.Core.Internal.Logic (Logic(..), LogicType(..), Var, Reified, Constructor(..), Field(..))

-- DSL: Fresh variables and type aliases
import TypedRedex.DSL.Fresh (L, Var', fresh, fresh2, fresh3, fresh4, fresh5, argument, argument2, argument3, argument4, argument5)

-- DSL: Define judgment/rule syntax
import TypedRedex.DSL.Define (Applied(..), Applied2(..), Applied3(..), Applied4(..), Applied5(..), Conclude(..), Premise(..), Rule(..), Rule2(..), Rule3(..), Rule4(..), Rule5(..), rule, rule1, rule2, rule3, rule4, rule5, judgment, judgment2, judgment3, judgment4, judgment5)

-- Relation primitives
import TypedRedex.Core.Internal.Relation (relation, relation2, relation3, relation4, relation5, call, premise, embed, (===), (<=>), conde)

-- Evaluation and running
import TypedRedex.Interp.Run (eval, run, run2, run3, run4, run5)

-- Negation (from Core)
import TypedRedex.Core.Internal.Redex (neg)
