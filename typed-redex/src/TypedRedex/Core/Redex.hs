-- | TypedRedex.Core.Redex: Main API for TypedRedex
--
-- This module provides the user-facing API for writing logic programs.
-- TypedRedex is a shallow embedding of PLT Redex in Haskell with a
-- Kanren-like solver, enabling direct use of Haskell's control flow,
-- pattern matching, and modularity.
--
-- Key concepts:
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
-- 4. **Unification** (===): Equate two logic terms
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

module TypedRedex.Core.Redex
(
  -- * Core types
  Relation(..)          -- ^ Named logic relations with name, args, and body
, Redex(RVar)           -- ^ Typeclass for logic programming monads
, RedexEval             -- ^ Extract ground values from logic terms
, RedexNeg              -- ^ Negation support
, LogicType             -- ^ Types that can be used in logic programs
, L                     -- ^ Logic terms: Free (variable) or Ground (value)

  -- * Creating fresh variables
  -- | Allocate unbound logic variables (∃ quantification)
, fresh, fresh2, fresh3, fresh4, fresh5

  -- * Defining relations
  -- | Build named relations from Haskell functions
  -- relation2 :: String -> (L a rel -> L b rel -> Relation rel) -> ...
, relation, relation2, relation3, relation4, relation5

  -- * Defining inference rules (for derivation tracking)
  -- | Build relations in rule style with conclusion patterns
  -- rule3 :: String -> ((L a rel -> L b rel -> L c rel -> Relation rel)
  --                      -> Relation rel) -> ...
, rule, rule2, rule3, rule4, rule5

  -- * Axioms (rules with no premises)
, axiom, axiom2, axiom3, axiom4

  -- * Combining multiple rules
  -- | Try multiple rules in order (disjunction)
, rules, rules2, rules3, rules4

  -- * Invoking relations
, call   -- ^ Invoke a relation (goal call)
, premise -- alias
, embed  -- ^ Embed a monadic computation as a goal

  -- * Evaluation
, eval   -- ^ Extract ground value from a logic term

  -- * Running logic programs
  -- | Execute relations and return streams of solutions
  -- run :: (forall rel. Redex rel => Relation rel -> rel a) -> Stream a
, run, run2, run3, run4, run5

  -- * Unification and relational operators
, (===)  -- ^ Unify two logic terms (equality constraint)
, (<=>)  -- ^ Apply a relation to arguments (deprecated: use call)

  -- * Disjunction
, conde  -- ^ Disjunction: try multiple goal clauses

  -- * Negation
, neg    -- ^ Constructive negation: succeed if goal has no solutions

  -- * Clean DSL syntax (define/concl/prem)
, Applied(..), Applied2(..), Applied3(..), Applied4(..), Applied5(..)
, Conclude(..)  -- concl method + ConcludePat type family
, Premise(..)   -- prem method
, define, define2, define3, define4, define5
) where

import TypedRedex.Core.Internal.Redex
import TypedRedex.Utils.Redex
import TypedRedex.Utils.Rule
import TypedRedex.Utils.Define
import TypedRedex.Core.Internal.Logic
