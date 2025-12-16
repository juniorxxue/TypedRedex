{-# LANGUAGE TypeFamilies, DeriveFunctor, Rank2Types, GeneralisedNewtypeDeriving, TypeSynonymInstances, MultiParamTypeClasses, FlexibleContexts #-}

-- | SubstRedex: A substitution-based interpreter for TypedRedex
--
-- = Overview
--
-- This is the standard "eval" interpreter that actually executes logic programs.
-- It implements search via substitutions and backtracking streams.
--
-- = Architecture
--
-- @
-- SubstRedex s a = StateT (Subst s) Stream a
--                   ├─ State: substitution + fresh variable counter
--                   └─ Stream: lazy list with interleaving for fair search
-- @
--
-- = Key Design Decisions
--
-- 1. **Triangular substitution**: Variables map to terms (which may contain variables)
--    @x ↦ app y z@ means x is bound to @app y z@, where y,z may be unbound
--
-- 2. **ST-style phantom type**: The @s@ parameter prevents variable escape
--    @runSubstRedex :: (forall s. SubstRedex s a) -> Stream a@
--
-- 3. **Fair interleaving**: 'suspend' wraps computation in 'Immature' thunk
--    This allows the scheduler to fairly explore all branches
--
-- = Implementing Redex
--
-- This interpreter implements:
--
-- * 'fresh_': Allocate integer-named variables
-- * 'unify': Triangular substitution with occurs check
-- * 'suspend': Wrap in 'Immature' for fair scheduling
-- * 'displayVar': Show as x0, x1, x2, ...
--
-- It does NOT need to implement the structure tracking hooks
-- ('onRuleEnter', 'onRuleExit', 'withPremise') since it doesn't
-- build derivation trees.

module TypedRedex.Interpreters.SubstRedex
  ( -- * Running Logic Programs
    runSubstRedex
    -- * Stream Operations
  , Stream
  , takeS
  , takeWhileS
  ) where

import TypedRedex.Core.Internal.Redex
import Stream
import Control.Monad.State
import Unsafe.Coerce (unsafeCoerce)
import TypedRedex.Utils.Redex

-- | Variable representation: just an integer
-- We'll wrap this in SVar (defined in Redex instance below)
type VarRepr = Int

-- | Type alias for variables in this interpreter
type V s t = RVar (SubstRedex s) t

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

-- | The SubstRedex monad: StateT over Stream
-- Combines:
--   - State: threading substitution through computation
--   - Stream: non-determinism with interleaving (fair conjunction/disjunction)
--   - Phantom 's': prevents mixing variables from different runs
newtype SubstRedex s a = SubstRedex (StateT (Subst s) Stream a) deriving (Functor, Applicative, Alternative, Monad)

-- | Short alias for convenience
type R s = SubstRedex s

-- | Make SubstRedex an instance of MonadState for convenient state access
instance MonadState (Subst s) (R s) where
    state = SubstRedex . state

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

-- | Redex instance: core logic programming operations
instance Redex (R s) where

    -- | Variables are just wrapped integers
    newtype instance (RVar (R s)) t = SVar VarRepr deriving (Functor, Show)

    -- | fresh_: allocate fresh variables
    fresh_ FreshVar   = (makeVar Nothing >>=)
    fresh_ (ArgVar x) = (makeVar (Just x) >>=)

    -- | unify: equate two logic terms
    unify = flatteningUnify unif
        where
            unif v y | occursCheck v y = empty
                     | otherwise = do
                        x <- readVar v
                        maybe (modify $ updateSubst v (Just y))
                              (unify y)
                              x

    -- | displayVar: pretty-print variables
    displayVar (SVar v) = "x" ++ show v

    -- | suspend: wrap in Immature for fair interleaving
    suspend (SubstRedex r) = SubstRedex $ mapStateT Immature r

-- | RedexEval: extract concrete values from logic terms
-- Used to get results after solving
instance RedexEval (R s) where

    -- | derefVar: fully dereference a variable to its ground value
    -- Follows the chain: v → binding → binding → ... → ground term
    -- Fails if variable is unbound (should not happen after successful solve)
    derefVar v = do
        x <- gets $ readSubst v
        maybe (error $ "Unbound variable: " ++ displayVar v) eval x

-- | EqVar: equality for variables (needed for occurs check and substitution lookup)
instance EqVar (R s) where
    varEq (SVar a) (SVar b) = a == b


-- | runSubstRedex: execute a logic program and return stream of results
-- The rank-2 type (forall s. R s t) ensures variables don't escape
-- (similar to runST in ST monad)
-- Returns: Stream t - potentially infinite stream of solutions
runSubstRedex :: (forall s. R s t) -> Stream t
runSubstRedex (SubstRedex r) = evalStateT r emptySubst
