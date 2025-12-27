{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}

-- | Eval Interpreter for Indexed Free Monad DSL
--
-- This interpreter executes rules using substitution-based logic programming.
-- It traverses the 'IxFree' AST and:
--
-- 1. Allocates fresh variables for 'FreshF'
-- 2. Unifies conclusion patterns with caller arguments for 'ConclF'
-- 3. Collects premises for scheduling for 'PremF'
-- 4. Schedules and executes premises in dependency order
--
-- = Key Insight
--
-- The AST (IxFree) is a pure data structure. Interpretation happens here,
-- giving us full control over execution order, scheduling, and effects.
--
-- = Usage
--
-- @
-- import TypedRedex.Free.Interp.Eval (interpretEval)
--
-- -- In your judgment definition:
-- mkAppliedM modes args rules = AppliedM
--   { amGoal = asum [ interpretEval args (mrAST rule args) | rule <- rules ]
--   , ...
--   }
-- @
module TypedRedex.Free.Interp.Eval
  ( -- * Interpretation
    interpretEval
  , interpretRule
    -- * Premise Scheduling
  , PremAction(..)
  , NegAction(..)
  , DeferredAction(..)
  , schedulePremises
  ) where

import qualified Prelude
import Prelude hiding ((>>=), (>>), return)
import Data.Set (Set)
import qualified Data.Set as S

import TypedRedex.Free.Logic
  ( LogicType, Logic(..), Redex(..), RedexNeg(..)
  , RVar, FreshType(..), Var(..)
  )
import TypedRedex.Free.IxFree (IxFree(..))
import TypedRedex.Free.RuleF
import TypedRedex.Free.Schedule (St(..))

--------------------------------------------------------------------------------
-- Deferred Actions
--------------------------------------------------------------------------------

-- | A premise action to be scheduled
data PremAction rel = PremAction
  { paReq  :: Set Int  -- ^ Required variables (inputs)
  , paProd :: Set Int  -- ^ Produced variables (outputs)
  , paGoal :: rel ()   -- ^ Goal to execute
  }

-- | A negation action
data NegAction rel = NegAction
  { naReq  :: Set Int  -- ^ Required variables
  , naGoal :: rel ()   -- ^ Goal to negate
  }

-- | A deferred action
data DeferredAction rel
  = PremA (PremAction rel)
  | NegA (NegAction rel)
  | LiftedA (rel ())

--------------------------------------------------------------------------------
-- Interpretation State
--------------------------------------------------------------------------------

-- | State during interpretation
data InterpState rel = InterpState
  { isNextVar   :: Int           -- ^ Next fresh variable ID
  , isAvailVars :: Set Int       -- ^ Variables available (grounded)
  , isDeferred  :: [DeferredAction rel]  -- ^ Collected deferred actions
  }

emptyState :: InterpState rel
emptyState = InterpState 0 S.empty []

--------------------------------------------------------------------------------
-- Main Interpretation
--------------------------------------------------------------------------------

-- | Interpret a rule AST
--
-- This is the main entry point for the eval interpreter.
interpretEval :: forall rel ts vss n steps.
                 (RedexNeg rel, ToLTermList vss ts)
              => TArgs vss ts rel                                    -- ^ Caller's arguments
              -> IxFree (RuleF rel ts) ('St 0 '[] 'False) ('St n steps 'True) ()  -- ^ Rule AST
              -> rel ()
interpretEval callerArgs ast = do
  -- Phase 1: Traverse AST, execute concl, collect deferred
  let callerLList = toLTermList callerArgs
  ((), finalState) <- runInterp callerLList ast emptyState

  -- Phase 2: Schedule and execute premises
  let deferred = reverse (isDeferred finalState)
      (prems, negs, lifted) = partitionDeferred deferred

  schedulePremises (isAvailVars finalState) prems

  -- Phase 3: Execute negations
  executeNegations negs

  -- Phase 4: Execute lifted actions
  executeLifted lifted

-- | Alias for compatibility
interpretRule :: (RedexNeg rel, ToLTermList vss ts)
              => TArgs vss ts rel
              -> IxFree (RuleF rel ts) ('St 0 '[] 'False) ('St n steps 'True) ()
              -> rel ()
interpretRule callerArgs ast = do
  let callerLList = toLTermList callerArgs
  ((), finalState) <- runInterp callerLList ast emptyState
  let deferred = reverse (isDeferred finalState)
      (prems, negs, lifted) = partitionDeferred deferred
  schedulePremises (isAvailVars finalState) prems
  executeNegations negs
  executeLifted lifted

--------------------------------------------------------------------------------
-- AST Traversal
--------------------------------------------------------------------------------

-- | Run interpretation, threading state through
runInterp :: forall rel ts s t a.
             (RedexNeg rel)
          => LTermList rel ts
          -> IxFree (RuleF rel ts) s t a
          -> InterpState rel
          -> rel (a, InterpState rel)

runInterp _ (Pure a) st = pure (a, st)

runInterp callerArgs (Bind op k) st = case op of

  -- FreshF: allocate a fresh variable
  FreshF -> do
    let varId = isNextVar st
    fresh_ FreshVar $ \v -> do
      let term = T (S.singleton varId) (Free v)
          st' = st { isNextVar = varId + 1 }
      runInterp callerArgs (k term) st'

  -- ConclF: unify with caller's arguments, mark inputs as available
  ConclF applied -> do
    -- Unify the applied pattern with caller's arguments
    unifyLList (amArgs applied) callerArgs
    -- Update available vars with conclusion's inputs
    let st' = st { isAvailVars = amReqVars applied }
    runInterp callerArgs (k ()) st'

  -- PremF: collect for later scheduling
  PremF applied -> do
    let action = PremA $ PremAction (amReqVars applied) (amProdVars applied) (amGoal applied)
        st' = st { isDeferred = action : isDeferred st }
    runInterp callerArgs (k ()) st'

  -- NegF: collect for later execution
  NegF applied -> do
    let action = NegA $ NegAction (S.union (amReqVars applied) (amProdVars applied)) (amGoal applied)
        st' = st { isDeferred = action : isDeferred st }
    runInterp callerArgs (k ()) st'

  -- UnifyF: collect unification as a premise
  UnifyF t1 t2 -> do
    let action = PremA $ PremAction (S.union (tVars t1) (tVars t2)) S.empty (unify (tTerm t1) (tTerm t2))
        st' = st { isDeferred = action : isDeferred st }
    runInterp callerArgs (k ()) st'

  -- NeqF: collect disequality as a premise (using negation)
  NeqF t1 t2 -> do
    let action = PremA $ PremAction (S.union (tVars t1) (tVars t2)) S.empty (neg (unify (tTerm t1) (tTerm t2)))
        st' = st { isDeferred = action : isDeferred st }
    runInterp callerArgs (k ()) st'

  -- LiftRelF: execute immediately
  LiftRelF action -> do
    result <- action
    runInterp callerArgs (k result) st

  -- LiftRelDeferredF: collect for later
  LiftRelDeferredF action -> do
    let st' = st { isDeferred = LiftedA action : isDeferred st }
    runInterp callerArgs (k ()) st'

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

-- | Unify two LTermLists element-wise
unifyLList :: (Redex rel) => LTermList rel ts -> LTermList rel ts -> rel ()
unifyLList TNil TNil = pure ()
unifyLList (x :> xs) (y :> ys) = unify x y Prelude.>> unifyLList xs ys

--------------------------------------------------------------------------------
-- Scheduling
--------------------------------------------------------------------------------

-- | Partition deferred actions by type
partitionDeferred :: [DeferredAction rel] -> ([PremAction rel], [NegAction rel], [rel ()])
partitionDeferred = foldr go ([], [], [])
  where
    go (PremA p)   (ps, ns, ls) = (p:ps, ns, ls)
    go (NegA n)    (ps, ns, ls) = (ps, n:ns, ls)
    go (LiftedA l) (ps, ns, ls) = (ps, ns, l:ls)

-- | Schedule premises based on data dependencies
--
-- Premises are executed in an order such that each premise's
-- required variables are available when it runs.
schedulePremises :: Redex rel => Set Int -> [PremAction rel] -> rel ()
schedulePremises _ [] = pure ()
schedulePremises avail prems =
  case selectReady avail prems of
    Just (ready, rest) -> do
      paGoal ready
      schedulePremises (S.union avail (paProd ready)) rest
    Nothing ->
      -- Should never happen if CheckSchedule passed
      error "Runtime scheduling failed: no ready premises"

-- | Select a premise whose inputs are all available
selectReady :: Set Int -> [PremAction rel] -> Maybe (PremAction rel, [PremAction rel])
selectReady _ [] = Nothing
selectReady avail (p:ps)
  | paReq p `S.isSubsetOf` avail = Just (p, ps)
  | otherwise = case selectReady avail ps of
      Nothing -> Nothing
      Just (ready, rest) -> Just (ready, p : rest)

-- | Execute negations in order
executeNegations :: RedexNeg rel => [NegAction rel] -> rel ()
executeNegations [] = pure ()
executeNegations (n:ns) = neg (naGoal n) Prelude.>> executeNegations ns

-- | Execute lifted actions in order
executeLifted :: Redex rel => [rel ()] -> rel ()
executeLifted [] = pure ()
executeLifted (a:as) = a Prelude.>> executeLifted as
