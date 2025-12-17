{-# LANGUAGE Rank2Types #-}

-- | Internal unification helpers for interpreters.
--
-- This module provides shared unification and evaluation helpers
-- used by SubstRedex and TracingRedex interpreters.
module TypedRedex.Core.Internal.Unify
  ( -- * Unification helpers
    flatteningUnify
    -- * Occurs check
  , occursCheck
    -- * Evaluation helpers
  , evalFromRead
  ) where

import TypedRedex.Core.Internal.Redex
import TypedRedex.Core.Internal.Logic
import Data.Maybe (fromMaybe)

-- | Flattening unification: handle Free/Ground cases, delegate Ground/Ground to unifyVal.
flatteningUnify :: (Alternative rel, LogicType a)
                => (forall a'. (LogicType a') => Var a' (RVar rel) -> Logic a' (RVar rel) -> rel ())
                -> Logic a (RVar rel)
                -> Logic a (RVar rel)
                -> rel ()
flatteningUnify unifyVar (Free a) b = unifyVar a b
flatteningUnify unifyVar a (Free b) = unifyVar b a
flatteningUnify unifyVar (Ground a) (Ground b) = unifyVal (flatteningUnify unifyVar) a b

-- | Check if a variable occurs in a logic term (occurs check).
occursCheck :: (LogicType b, EqVar rel) => Var a (RVar rel) -> Logic b (RVar rel) -> Bool
occursCheck x (Free y) = x `varEq` y
occursCheck x (Ground y) = let (_, ys) = quote y in any (\(Field _ y') -> occursCheck x y') ys

-- | Build eval from a variable-reading function.
evalFromRead :: (Redex rel, LogicType a)
             => (forall a'. (LogicType a') => Var a' (RVar rel) -> rel (Maybe a'))
             -> Logic a (RVar rel)
             -> rel a
evalFromRead readVar (Ground x) = derefVal (evalFromRead readVar) x
evalFromRead readVar (Free v) = do
    x <- readVar v
    pure $ fromMaybe (error $ "Unbound variable: " ++ displayVar v) x
