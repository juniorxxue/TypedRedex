{-# LANGUAGE TypeFamilies, DeriveFunctor, Rank2Types, GeneralisedNewtypeDeriving, TypeSynonymInstances, MultiParamTypeClasses, FlexibleContexts #-}

-- | SubstKanren: A substitution-based interpreter for miniKanren
--
-- This interpreter implements logic programming via explicit substitutions.
-- Key design decisions:
--
-- 1. **Substitution representation**: Maps variables to their bindings (triangular substitution)
--    - Unbound variables are not in the map
--    - Bindings can contain other variables (transitive lookups needed)
--
-- 2. **Variable identity**: Uses Int-based variable names with phantom type parameter s
--    - The 's' parameter prevents variable leakage across different runs (ST monad trick)
--
-- 3. **Monad stack**: StateT (Subst s) Stream
--    - State: maintains current substitution and next fresh variable counter
--    - Stream: provides backtracking and interleaving search
--
-- 4. **Interleaving**: call_ uses 'Immature' to suspend computation, enabling fair scheduling

module Shallow.Interpreters.SubstKanren
(
  runSubstKanren
, Stream
, takeS
, takeWhileS
) where

import Shallow.Core.Internal.Kanren
import Stream
import Control.Monad.State
import Unsafe.Coerce (unsafeCoerce)
import Shallow.Utils.Kanren

-- | Variable representation: just an integer
-- We'll wrap this in SVar (defined in Kanren instance below)
type VarRepr = Int

-- | Type alias for variables in this interpreter
type V s t = KVar (SubstKanren s) t

-- | Substitution: a map from variables to their bindings
-- Uses rank-2 polymorphism to make it heterogeneous (variables of different types)
data Subst s = Subst { subst :: forall t. V s t -> Maybe t, nextVar :: VarRepr }

-- | Empty substitution with no bindings
-- Variables start from 0; accessing unbound variables is an error
emptySubst :: Subst s
emptySubst = Subst { subst = \v -> error $ "Invalid variable " ++ displayVar v, nextVar = toEnum 0 }

-- | Look up a variable in the substitution
-- Returns Nothing if unbound, Just t if bound to t
readSubst :: V s a -> Subst s -> Maybe a
readSubst v s = subst s v

-- | Extend substitution with a new binding: v ↦ a
-- Creates a new substitution function that checks for v first, then delegates to old one
-- Note: Uses unsafeCoerce because v' could have different type than v
updateSubst :: V s a -> Maybe a -> Subst s -> Subst s
updateSubst v a s = s { subst = \v' -> if v `varEq` v' then unsafeCoerce a else subst s v' }

-- | Increment the fresh variable counter
succVar :: Subst s -> Subst s
succVar s = s { nextVar = succ (nextVar s) }

-- | The SubstKanren monad: StateT over Stream
-- Combines:
--   - State: threading substitution through computation
--   - Stream: non-determinism with interleaving (fair conjunction/disjunction)
--   - Phantom 's': prevents mixing variables from different runs
newtype SubstKanren s a = SubstKanren (StateT (Subst s) Stream a) deriving (Functor, Applicative, Alternative, Monad)

-- | Short alias for convenience
type R s = SubstKanren s

-- | Make SubstKanren an instance of MonadState for convenient state access
instance MonadState (Subst s) (R s) where
    state = SubstKanren . state

-- | Look up variable's binding in current substitution
readVar :: V s t -> R s (Maybe t)
readVar v = gets $ readSubst v

-- | Allocate a fresh variable with optional initial binding
-- The binding x is used for "argument variables" (when embedding ground terms)
makeVar :: Maybe (L a (R s)) -> R s (Var' a (R s))
makeVar x = do
    v <- SVar <$> gets nextVar          -- Get next available variable number
    modify $ succVar . updateSubst v x  -- Increment counter and add binding
    return $ v

-- | Kanren instance: implements logic programming operations
instance Kanren (R s) where

    -- | Variables are just wrapped integers
    -- The phantom type parameter t prevents mixing variables of different types
    newtype instance (KVar (R s)) t = SVar VarRepr deriving (Functor, Show)

    -- | fresh_: allocate fresh variables
    -- FreshVar: completely unbound (for ∃)
    -- ArgVar x: pre-bound to x (for embedding ground terms)
    fresh_ FreshVar   = (makeVar Nothing >>=)
    fresh_ (ArgVar x) = (makeVar (Just x) >>=)

    -- | unify: equate two logic terms under current substitution
    -- Uses flatteningUnify (from Utils) to handle nested Free/Ground constructors
    -- Then delegates to unif for variable-term unification
    unify = flatteningUnify unif
        where
            -- unif v y: unify variable v with term y
            unif v y | occursCheck v y = empty          -- Fail if v occurs in y (prevents infinite terms)
                     | otherwise = do
                        x <- readVar v                   -- Check if v already bound
                        maybe (modify $ updateSubst v (Just y))  -- Unbound: bind v ↦ y
                              (unify y)                  -- Bound to x: recursively unify y with x
                              x

    -- | call_: invoke a relation (goal)
    -- Opaque: wrap in Immature to suspend computation (enables interleaving)
    --   This is crucial for fairness: prevents one branch from running forever
    --   before trying other branches
    -- Transparent: run directly without suspension (for internal relations)
    call_ Opaque (Relation _ (SubstKanren r)) = SubstKanren $ mapStateT Immature r
    call_ Transparent (Relation _ r) = r

    -- | displayVar: pretty-print variables as x0, x1, x2, ...
    displayVar (SVar v) = "x" ++ show v

-- | KanrenEval: extract concrete values from logic terms
-- Used to get results after solving
instance KanrenEval (R s) where

    -- | derefVar: fully dereference a variable to its ground value
    -- Follows the chain: v → binding → binding → ... → ground term
    -- Fails if variable is unbound (should not happen after successful solve)
    derefVar v = do
        x <- gets $ readSubst v
        maybe (error $ "Unbound variable: " ++ displayVar v) eval x

-- | EqVar: equality for variables (needed for occurs check and substitution lookup)
instance EqVar (R s) where
    varEq (SVar a) (SVar b) = a == b


-- | runSubstKanren: execute a logic program and return stream of results
-- The rank-2 type (forall s. R s t) ensures variables don't escape
-- (similar to runST in ST monad)
-- Returns: Stream t - potentially infinite stream of solutions
runSubstKanren :: (forall s. R s t) -> Stream t
runSubstKanren (SubstKanren r) = evalStateT r emptySubst
