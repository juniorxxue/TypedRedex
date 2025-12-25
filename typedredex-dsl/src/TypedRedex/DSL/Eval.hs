{-# LANGUAGE ApplicativeDo #-}

-- | Relation execution utilities.
--
-- This module provides combinators for running relations and extracting
-- ground values from the resulting substitutions.
module TypedRedex.DSL.Eval
  ( -- * Evaluation
    eval
    -- * Running relations
  , run, run2, run3, run4, run5
  ) where

import TypedRedex.Logic
import TypedRedex.DSL.Fresh
import TypedRedex.DSL.Relation (callDirect)

--------------------------------------------------------------------------------
-- Evaluation
--------------------------------------------------------------------------------

-- | Extract a ground value from a logic term.
eval :: (RedexEval rel, LogicType a) => LTerm a rel -> rel a
eval (Free v) = derefVar v
eval (Ground x) = derefVal eval x

--------------------------------------------------------------------------------
-- Running relations
--------------------------------------------------------------------------------

-- | Run a unary relation and extract the result.
run :: (RedexEval rel, LogicType a) => (LTerm a rel -> Relation rel) -> rel a
run f = fresh $ \x -> do
    _ <- callDirect $ f x
    x' <- eval x
    return x'

-- | Run a binary relation and extract both results.
run2 :: (RedexEval rel, LogicType a, LogicType b) => (LTerm a rel -> LTerm b rel -> Relation rel) -> rel (a, b)
run2 f = fresh2 $ \x y -> do
    _ <- callDirect $ f x y
    a <- eval x
    b <- eval y
    return (a, b)

-- | Run a ternary relation and extract all results.
run3 :: (RedexEval rel, LogicType a, LogicType b, LogicType c) => (LTerm a rel -> LTerm b rel -> LTerm c rel -> Relation rel) -> rel (a, b, c)
run3 f = fresh3 $ \x y z -> do
    _ <- callDirect $ f x y z
    a <- eval x
    b <- eval y
    c <- eval z
    return (a, b, c)

-- | Run a quaternary relation and extract all results.
run4 :: (RedexEval rel, LogicType a, LogicType b, LogicType c, LogicType d) => (LTerm a rel -> LTerm b rel -> LTerm c rel -> LTerm d rel -> Relation rel) -> rel (a, b, c, d)
run4 f = fresh4 $ \x y z w -> do
    _ <- callDirect $ f x y z w
    a <- eval x
    b <- eval y
    c <- eval z
    d <- eval w
    return (a, b, c, d)

-- | Run a 5-ary relation and extract all results.
run5 :: (RedexEval rel, LogicType a, LogicType b, LogicType c, LogicType d, LogicType e) => (LTerm a rel -> LTerm b rel -> LTerm c rel -> LTerm d rel -> LTerm e rel -> Relation rel) -> rel (a, b, c, d, e)
run5 f = fresh5 $ \x y z w q -> do
    _ <- callDirect $ f x y z w q
    a <- eval x
    b <- eval y
    c <- eval z
    d <- eval w
    e <- eval q
    return (a, b, c, d, e)
