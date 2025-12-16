-- | Shallow.Core.Kanren: Main API for shallow-embedded miniKanren
--
-- This module provides the user-facing API for writing logic programs.
-- "Shallow embedding" means relations are Haskell functions (not data structures),
-- enabling direct use of Haskell's control flow, pattern matching, and modularity.
--
-- Key concepts:
--
-- 1. **Relations** (Relation rel): Logic predicates that can succeed with multiple solutions
--    - Think of them as non-deterministic boolean functions
--    - Can be called, unified, and composed
--
-- 2. **Logic variables** (KVar): Unification variables (like Prolog variables)
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
--    - SubstKanren: substitution-based with interleaving
--    - TracingKanren: tracks derivation trees for proof output

module Shallow.Core.Kanren
(
  -- * Core types
  Relation(Relation)  -- ^ Named logic relations (predicates)
, Kanren(KVar)        -- ^ Typeclass for logic programming monads
, KanrenEval          -- ^ Extract ground values from logic terms
, LogicType           -- ^ Types that can be used in logic programs
, L                   -- ^ Logic terms: Free (variable) or Ground (value)

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
, embed  -- ^ Embed a monadic computation as a goal

  -- * Evaluation
, eval   -- ^ Extract ground value from a logic term

  -- * Running logic programs
  -- | Execute relations and return streams of solutions
  -- run :: (forall rel. Kanren rel => Relation rel -> rel a) -> Stream a
, run, run2, run3, run4, run5

  -- * Unification and relational operators
, (===)  -- ^ Unify two logic terms (equality constraint)
, (<=>)  -- ^ Apply a relation to arguments (deprecated: use call)

  -- * Disjunction
, conde  -- ^ Disjunction: try multiple goal clauses
) where

import Shallow.Core.Internal.Kanren
import Shallow.Utils.Kanren
import Shallow.Utils.Rule
import Shallow.Core.Internal.Logic