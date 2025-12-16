{-# LANGUAGE GADTs, KindSignatures, FlexibleContexts, TypeFamilies #-}

-- | Internal.Kanren: Core typeclass and interface for miniKanren interpreters
--
-- This module defines the abstract interface that all Kanren interpreters must implement.
-- Different interpreters (SubstKanren, TracingKanren) provide different implementations
-- of these operations, but all use the same interface for writing relations.
--
-- Key design patterns:
--
-- 1. **Type families**: KVar rel is an associated type, allowing different interpreters
--    to use different variable representations (e.g., Int-based, name-based)
--
-- 2. **Higher-kinded types**: rel :: Type -> Type is the monad implementing logic programming
--    Combines Alternative (for disjunction) with Monad (for conjunction)
--
-- 3. **GADTs for fresh variables**: FreshType distinguishes between:
--    - Completely unbound variables (FreshVar)
--    - Pre-bound argument variables for embedding (ArgVar)
--
-- 4. **Rank-2 polymorphism**: fresh_ uses (forall t. ...) to ensure variables
--    don't escape their scope (like ST monad)

module Shallow.Core.Internal.Kanren(module Shallow.Core.Internal.Kanren, Alternative(empty, (<|>)), EqVar(varEq)) where

import Data.Kind (Type)
import Control.Applicative (Alternative(empty, (<|>)))
import Shallow.Core.Internal.Logic

-- | Relation: A named logic relation (predicate)
--
-- Relations are the fundamental building blocks of logic programs.
-- Components:
--   - String: relation name (for debugging, tracing, derivation trees)
--   - rel (): the computation that implements the relation
--
-- Example: Relation "append" (appendImpl ctx1 ctx2 ctx3)
--
-- Note: Returns () because success/failure is via Alternative (empty vs pure ())
data Relation (rel :: Type -> Type) = Relation String (rel ())

-- | FreshType: How to allocate a fresh variable
--
-- Two modes:
--   1. FreshVar: Completely unbound, for existential quantification (∃x. ...)
--      Used when writing: fresh $ \x -> ...
--
--   2. ArgVar: Pre-bound to a logic term, for embedding ground terms
--      Used internally when projecting Haskell values into logic
--      Example: project (Nat 3) creates a variable pre-bound to Ground 3
data FreshType (rel :: Type -> Type) (t :: Type) where
    FreshVar :: FreshType rel t
    ArgVar :: (Kanren rel, LogicType t) => Logic t (KVar rel) -> FreshType rel t

-- | CallType: How to invoke a relation
--
-- Opaque: Standard goal call with suspension point (for interleaving)
--   - Ensures fair scheduling: prevents one branch from running forever
--   - Used for user-defined relations
--
-- Transparent: Direct execution without suspension
--   - Used for primitive operations that should not introduce delay
--   - Used for internal relations that need immediate execution
data CallType = Opaque | Transparent

-- | Kanren: The core typeclass for logic programming interpreters
--
-- Every interpreter (SubstKanren, TracingKanren, etc.) must implement this interface.
--
-- Superclasses:
--   - Monad rel: For conjunction (sequencing goals with >>=)
--   - Alternative rel: For disjunction (trying alternatives with <|>, failure with empty)
--   - Functor (KVar rel): Variables can be mapped over (for occurs check, etc.)
--
-- The interpreter must provide:
--   1. Variable representation (KVar)
--   2. Variable allocation (fresh_)
--   3. Unification (unify)
--   4. Relation invocation (call_)
--   5. Pretty-printing (displayVar)
--   6. Optional hooks (onRelationCall)
class (Monad rel, Alternative rel, Functor (KVar rel)) => Kanren rel where

    -- | KVar: Type family for logic variables
    -- Each interpreter chooses its own representation:
    --   - SubstKanren: SVar Int (integer-based names)
    --   - TracingKanren: TVar Int (with additional tracking)
    --
    -- The phantom type parameter 't' ensures type safety:
    --   KVar rel Nat is different from KVar rel Ty
    data KVar rel :: Type -> Type

    -- | fresh_: Allocate a fresh logic variable
    --
    -- Type signature: FreshType rel t -> (Var t (KVar rel) -> rel a) -> rel a
    --
    -- This is the primitive for ∃ quantification. The continuation receives
    -- the fresh variable and returns a computation using it.
    --
    -- FreshType determines whether the variable is:
    --   - FreshVar: unbound (normal case)
    --   - ArgVar logic_term: pre-bound to a term (for embedding)
    --
    -- The rank-2 type (with continuation) ensures the variable doesn't escape
    -- its scope, similar to ST monad's runST.
    fresh_ :: (LogicType t) => FreshType rel t -> (Var t (KVar rel) -> rel a) -> rel a

    -- | unify: Equate two logic terms (unification)
    --
    -- This is the core operation of logic programming (Prolog's '=').
    -- Attempts to make two terms equal by:
    --   1. Binding variables to terms
    --   2. Recursively unifying structured terms
    --   3. Checking ground terms for equality
    --
    -- Fails (empty) if unification is impossible:
    --   - Different constructors: unify (nat 3) (nat 5) fails
    --   - Occurs check: unify x (cons x tail) fails (would create infinite term)
    --
    -- Example: unify (Free x) (Ground (nat 3)) binds x to nat 3
    unify :: (LogicType a) => Logic a (KVar rel) -> Logic a (KVar rel) -> rel ()

    -- | call_: Invoke a relation (goal)
    --
    -- Two modes via CallType:
    --
    -- Opaque: Normal goal call with suspension point
    --   - Creates interleaving opportunity for fair scheduling
    --   - Example: call_ Opaque (Relation "append" impl)
    --   - SubstKanren wraps in 'Immature' to suspend computation
    --
    -- Transparent: Direct execution without suspension
    --   - For primitive operations that shouldn't introduce delay
    --   - Used internally by the system
    call_ :: CallType -> Relation rel -> rel ()

    -- | displayVar: Convert variable to readable string
    --
    -- Used for debugging, error messages, and pretty-printing.
    -- Typically: "x0", "x1", "x2", ...
    displayVar :: KVar rel t -> String

    -- | onRelationCall: Hook for capturing relation invocations
    --
    -- Called when a relation is invoked, BEFORE its body executes.
    -- Used by deep interpreters (like TracingKanren) to capture proof structure.
    --
    -- Parameters:
    --   - String: relation name (e.g., "⇒App", "lookup")
    --   - [String]: pretty-printed arguments (e.g., ["Γ", "e1 e2", "B"])
    --
    -- Default implementation: does nothing (for interpreters that don't need it)
    --
    -- TracingKanren uses this to push derivation frames onto a stack.
    onRelationCall :: String -> [String] -> rel ()
    onRelationCall _ _ = pure ()

-- | KanrenEval: Extract ground values from logic terms
--
-- This class provides the ability to evaluate logic terms to concrete values.
-- Used after solving to extract results from the stream.
--
-- Separate from Kanren because:
--   - Not all interpreters can evaluate (e.g., a constraint-collecting interpreter)
--   - Evaluation may fail if variables remain unbound
--
-- Example workflow:
--   1. Run logic program: runSubstKanren $ fresh $ \x -> ... produces Stream results
--   2. Extract value: eval (Free x) dereferences x to its ground value
class (Kanren rel) => KanrenEval rel where

    -- | derefVar: Fully dereference a variable to a ground value
    --
    -- Follows the chain of variable bindings until reaching a ground term:
    --   x → y → z → Ground value
    --
    -- This is the "walk*" operation in miniKanren terminology.
    --
    -- Fails with error if the variable is unbound (should not happen after
    -- successful solve, but can occur if you try to evaluate mid-computation)
    --
    -- Example: If x is bound to Ground (nat 3), then derefVar x returns 3
    derefVar :: (LogicType a) => Var a (KVar rel) -> rel a

-- | EqVar: Equality for logic variables
--
-- Needed for:
--   1. Occurs check: Does variable x appear in term t?
--   2. Substitution lookup: Is this the variable we're looking for?
--
-- Note: This compares variable identity (same variable?), not their values.
-- Variables with different identities are unequal even if bound to same value.
--
-- Example: varEq (SVar 0) (SVar 0) = True
--          varEq (SVar 0) (SVar 1) = False
class EqVar rel where

    -- | varEq: Test if two variables are the same
    --
    -- Type signature allows comparing variables of different types:
    --   varEq :: KVar rel a -> KVar rel b -> Bool
    -- This is safe because we're only comparing identities, not values.
    --
    -- Used in occurs check and substitution operations.
    varEq :: (KVar rel) a -> (KVar rel) b -> Bool