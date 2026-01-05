{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

-- | Relation execution utilities.
--
-- This module provides combinators for running relations and extracting
-- ground values from the resulting substitutions.
--
-- == Running moded judgments
--
-- Use 'run', 'run2', etc. with lambda-captured outputs:
--
-- @
-- -- 2 outputs: use run2
-- run2 $ \\ty env -> goal $ infer eempty cempty (lit 1) ty env
--
-- -- With ground Haskell values: use inject
-- run2 $ \\ty env -> goal $ infer (inject EEmpty) (inject CEmpty) (inject $ Literal 1) ty env
--
-- -- 1 output: use run
-- run $ \\env' -> goal $ ssub (inject env) (inject ty1) (inject pol) (inject ty2) env'
-- @
module TypedRedex.Interp.Run
  ( -- * Evaluation
    eval
    -- * Running moded judgments (lambda-captured outputs)
  , run, run2, run3, run4, run5
    -- * Helpers
  , inject
  , goal
  ) where

import qualified Data.Set as S

import TypedRedex.Logic
import TypedRedex.DSL.Fresh
import TypedRedex.DSL.Moded (T(..), AppliedM(..))
import TypedRedex.Interp.Subst (runSubstRedex)
import TypedRedex.Interp.Stream (Stream)

-- | Constraint alias for judgments that need full interpreter features
type FullRel rel = (Redex rel, RedexEval rel, RedexFresh rel, RedexNeg rel, RedexHash rel)

--------------------------------------------------------------------------------
-- Evaluation
--------------------------------------------------------------------------------

-- | Extract a ground value from a logic term.
eval :: (RedexEval rel, LogicType a) => LTerm a rel -> rel a
eval (Free v) = derefVar v
eval (Ground x) = derefVal eval x

--------------------------------------------------------------------------------
-- Core helpers
--------------------------------------------------------------------------------

-- | Inject a ground Haskell value into a moded term.
--
-- Use this to pass ground values to judgment inputs:
--
-- @
-- run2 $ \\ty env -> goal $ infer (inject EEmpty) (inject CEmpty) (inject $ Literal 1) ty env
-- @
inject :: LogicType a => a -> T '[] a rel
inject x = T S.empty (Ground (project x))

-- | Extract the goal from a moded judgment application.
--
-- @
-- run2 $ \\ty env -> goal $ infer eempty cempty (lit 1) ty env
-- @
goal :: AppliedM rel name modes vss ts -> rel ()
goal = amGoal

--------------------------------------------------------------------------------
-- Running moded judgments with lambda-captured outputs
--
-- Use run, run2, run3, etc. based on how many outputs you need.
-- The lambda parameters become fresh output variables.
--------------------------------------------------------------------------------

-- | Run a judgment with 1 output.
--
-- @
-- run $ \\env' -> goal $ ssub (inject env) (inject ty1) (inject pol) (inject ty2) env'
-- @
run :: LogicType a
    => (forall rel. FullRel rel => T '[] a rel -> rel ())
    -> Stream a
run f = runSubstRedex $ fresh $ \x -> do
  f (T S.empty x)
  eval x

-- | Run a judgment with 2 outputs.
--
-- @
-- run2 $ \\ty env -> goal $ infer eempty cempty (lit 1) ty env
-- @
run2 :: (LogicType a, LogicType b)
     => (forall rel. FullRel rel => T '[] a rel -> T '[] b rel -> rel ())
     -> Stream (a, b)
run2 f = runSubstRedex $ fresh2 $ \x y -> do
  f (T S.empty x) (T S.empty y)
  (,) <$> eval x <*> eval y

-- | Run a judgment with 3 outputs.
run3 :: (LogicType a, LogicType b, LogicType c)
     => (forall rel. FullRel rel => T '[] a rel -> T '[] b rel -> T '[] c rel -> rel ())
     -> Stream (a, b, c)
run3 f = runSubstRedex $ fresh3 $ \x y z -> do
  f (T S.empty x) (T S.empty y) (T S.empty z)
  (,,) <$> eval x <*> eval y <*> eval z

-- | Run a judgment with 4 outputs.
run4 :: (LogicType a, LogicType b, LogicType c, LogicType d)
     => (forall rel. FullRel rel => T '[] a rel -> T '[] b rel -> T '[] c rel -> T '[] d rel -> rel ())
     -> Stream (a, b, c, d)
run4 f = runSubstRedex $ fresh4 $ \x y z w -> do
  f (T S.empty x) (T S.empty y) (T S.empty z) (T S.empty w)
  (,,,) <$> eval x <*> eval y <*> eval z <*> eval w

-- | Run a judgment with 5 outputs.
run5 :: (LogicType a, LogicType b, LogicType c, LogicType d, LogicType e)
     => (forall rel. FullRel rel => T '[] a rel -> T '[] b rel -> T '[] c rel -> T '[] d rel -> T '[] e rel -> rel ())
     -> Stream (a, b, c, d, e)
run5 f = runSubstRedex $ fresh5 $ \x y z w q -> do
  f (T S.empty x) (T S.empty y) (T S.empty z) (T S.empty w) (T S.empty q)
  (,,,,) <$> eval x <*> eval y <*> eval z <*> eval w <*> eval q
