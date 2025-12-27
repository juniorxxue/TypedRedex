{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ExistentialQuantification #-}

-- | Tracing Interpreter for Indexed Free Monad DSL
--
-- This interpreter executes rules while building derivation trees.
-- It extends the eval interpreter with derivation tracking.
--
-- = Key Insight
--
-- The Free Monad structure makes it easy to add cross-cutting concerns
-- like tracing. We interpret the same AST differently, building up
-- derivation trees as we execute.
--
-- = Derivation Trees
--
-- @
-- Deriv "β" ["(λ.e) v", "e'"] [premise1, premise2]
-- represents:
--
--   premise1    premise2
--   ─────────────────────── [β]
--        (λ.e) v → e'
-- @
module TypedRedex.Free.Interp.Trace
  ( -- * Derivation Trees
    Derivation(..)
  , prettyDerivation
    -- * Interpretation
  , interpretTrace
    -- * Re-exports from Eval
  , PremAction(..)
  , NegAction(..)
  , DeferredAction(..)
  ) where

import qualified Prelude
import Prelude hiding ((>>=), (>>), return)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Proxy (Proxy(..))

import TypedRedex.Free.Logic
  ( LogicType(..), Logic(..), Redex(..), RedexNeg(..)
  , RVar, FreshType(..), Var(..), Field(..)
  )
import TypedRedex.Free.IxFree (IxFree(..))
import TypedRedex.Free.RuleF
import TypedRedex.Free.Schedule (St(..))
import TypedRedex.Free.Interp.Eval
  ( PremAction(..), NegAction(..), DeferredAction(..)
  , schedulePremises
  )

--------------------------------------------------------------------------------
-- Derivation Trees
--------------------------------------------------------------------------------

-- | A derivation tree representing a proof
data Derivation
  = Deriv
      { derivRule     :: String         -- ^ Rule name
      , derivArgs     :: [String]       -- ^ Arguments (pretty-printed)
      , derivChildren :: [Derivation]   -- ^ Premises (sub-derivations)
      }
  | Leaf String [String]                -- ^ Axiom
  deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Pretty-printing
--------------------------------------------------------------------------------

-- | Pretty-print a derivation tree
prettyDerivation :: Derivation -> String
prettyDerivation d = unlines $ renderDeriv d
  where
    renderDeriv :: Derivation -> [String]
    renderDeriv (Leaf name _) = [name]
    renderDeriv (Deriv "top" _ children) =
      case children of
        [c] -> renderDeriv c
        cs -> concatMap renderDeriv cs
    renderDeriv (Deriv name args children) =
      let conclusion = formatConclusion name args
          childBlocks = map renderDeriv children
      in if null childBlocks
         then
           let lineWidth = length conclusion + 4
               line = replicate lineWidth '─' ++ " [" ++ name ++ "]"
           in [line, conclusion]
         else
           let combined = foldr1 sideBySide childBlocks
               premiseWidth = if null combined then 0 else maximum (map length combined)
               concWidth = length conclusion
               lineWidth = max premiseWidth concWidth
               line = replicate lineWidth '─' ++ " [" ++ name ++ "]"
               concPad = (lineWidth - concWidth) `div` 2
               paddedConc = replicate concPad ' ' ++ conclusion
           in combined ++ [line, paddedConc]

    sideBySide :: [String] -> [String] -> [String]
    sideBySide left right =
      let leftWidth = if null left then 0 else maximum (map length left)
          leftHeight = length left
          rightHeight = length right
          maxHeight = max leftHeight rightHeight
          padLeft = replicate (maxHeight - leftHeight) (replicate leftWidth ' ')
                    ++ map (padRight leftWidth) left
          padRightBlock = replicate (maxHeight - rightHeight) "" ++ right
          spacing = "   "
      in zipWith (\l r -> l ++ spacing ++ r) padLeft padRightBlock

    padRight :: Int -> String -> String
    padRight n s = s ++ replicate (n - length s) ' '

    formatConclusion :: String -> [String] -> String
    formatConclusion name [] = name
    formatConclusion name as = name ++ "(" ++ intercalate ", " as ++ ")"

    intercalate :: String -> [String] -> String
    intercalate _ [] = ""
    intercalate _ [x] = x
    intercalate sep (x:xs) = x ++ sep ++ intercalate sep xs

--------------------------------------------------------------------------------
-- Tracing State
--------------------------------------------------------------------------------

-- | A captured term for deferred resolution
data CapturedForTrace rel = forall a. (LogicType a) => CapturedForTrace (Logic a (RVar rel))

-- | Derivation frame
data DerivFrame rel = DerivFrame
  { frameName     :: String
  , frameTerms    :: [CapturedForTrace rel]  -- ^ Captured for later resolution
  , frameChildren :: [Derivation]            -- ^ Accumulated premise derivations
  }

-- | Tracing state
data TraceState rel = TraceState
  { tsNextVar    :: Int
  , tsAvailVars  :: Set Int
  , tsDeferred   :: [DeferredAction rel]
  , tsDerivStack :: [DerivFrame rel]
  }

emptyTraceState :: TraceState rel
emptyTraceState = TraceState 0 S.empty [] [DerivFrame "top" [] []]

--------------------------------------------------------------------------------
-- Interpretation
--------------------------------------------------------------------------------

-- | Interpret a rule AST with tracing
interpretTrace :: forall rel ts vss n steps.
                  (RedexNeg rel, ToLTermList vss ts)
               => String                                                  -- ^ Rule name
               -> TArgs vss ts rel                                        -- ^ Caller's arguments
               -> IxFree (RuleF rel ts) ('St 0 '[] 'False) ('St n steps 'True) ()
               -> rel Derivation
interpretTrace ruleName callerArgs ast = do
  -- Phase 1: Traverse AST with tracing
  let callerLList = toLTermList callerArgs
  ((), finalState) <- runTrace callerLList ast (emptyTraceState { tsDerivStack = [DerivFrame ruleName [] []] })

  -- Phase 2: Schedule and execute premises (same as eval)
  let deferred = reverse (tsDeferred finalState)
      (prems, negs, lifted) = partitionDeferred deferred

  schedulePremises (tsAvailVars finalState) prems

  -- Phase 3: Execute negations
  executeNegations negs

  -- Phase 4: Execute lifted actions
  executeLifted lifted

  -- Phase 5: Build final derivation
  let stack = tsDerivStack finalState
  case stack of
    [frame] ->
      let args = [] -- Would resolve captured terms here
      in pure $ Deriv (frameName frame) args (reverse $ frameChildren frame)
    _ -> pure $ Leaf "?" []

-- | Run tracing interpretation
runTrace :: forall rel ts s t a.
            (RedexNeg rel)
         => LTermList rel ts
         -> IxFree (RuleF rel ts) s t a
         -> TraceState rel
         -> rel (a, TraceState rel)

runTrace _ (Pure a) st = pure (a, st)

runTrace callerArgs (Bind op k) st = case op of

  FreshF -> do
    let varId = tsNextVar st
    fresh_ FreshVar $ \v -> do
      let term = T (S.singleton varId) (Free v)
          st' = st { tsNextVar = varId + 1 }
      runTrace callerArgs (k term) st'

  ConclF applied -> do
    unifyLList (amArgs applied) callerArgs
    let st' = st { tsAvailVars = amReqVars applied }
    -- Capture terms for later resolution
    let captured = captureLTermList (amArgs applied)
        st'' = updateFrameTerms captured st'
    runTrace callerArgs (k ()) st''

  PremF applied -> do
    let action = PremA $ PremAction (amReqVars applied) (amProdVars applied) (amGoal applied)
        st' = st { tsDeferred = action : tsDeferred st }
    runTrace callerArgs (k ()) st'

  NegF applied -> do
    let action = NegA $ NegAction (S.union (amReqVars applied) (amProdVars applied)) (amGoal applied)
        st' = st { tsDeferred = action : tsDeferred st }
    runTrace callerArgs (k ()) st'

  UnifyF t1 t2 -> do
    let action = PremA $ PremAction (S.union (tVars t1) (tVars t2)) S.empty (unify (tTerm t1) (tTerm t2))
        st' = st { tsDeferred = action : tsDeferred st }
    runTrace callerArgs (k ()) st'

  NeqF t1 t2 -> do
    let action = PremA $ PremAction (S.union (tVars t1) (tVars t2)) S.empty (neg (unify (tTerm t1) (tTerm t2)))
        st' = st { tsDeferred = action : tsDeferred st }
    runTrace callerArgs (k ()) st'

  LiftRelF action -> do
    result <- action
    runTrace callerArgs (k result) st

  LiftRelDeferredF action -> do
    let st' = st { tsDeferred = LiftedA action : tsDeferred st }
    runTrace callerArgs (k ()) st'

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

-- | Unify two LTermLists
unifyLList :: (Redex rel) => LTermList rel ts -> LTermList rel ts -> rel ()
unifyLList TNil TNil = pure ()
unifyLList (x :> xs) (y :> ys) = unify x y Prelude.>> unifyLList xs ys

-- | Capture LTermList for tracing
captureLTermList :: LTermList rel ts -> [CapturedForTrace rel]
captureLTermList TNil = []
captureLTermList (x :> xs) = CapturedForTrace x : captureLTermList xs

-- | Update frame terms
updateFrameTerms :: [CapturedForTrace rel] -> TraceState rel -> TraceState rel
updateFrameTerms terms st = case tsDerivStack st of
  (frame : rest) -> st { tsDerivStack = frame { frameTerms = terms } : rest }
  [] -> st

-- | Partition deferred actions
partitionDeferred :: [DeferredAction rel] -> ([PremAction rel], [NegAction rel], [rel ()])
partitionDeferred = foldr go ([], [], [])
  where
    go (PremA p)   (ps, ns, ls) = (p:ps, ns, ls)
    go (NegA n)    (ps, ns, ls) = (ps, n:ns, ls)
    go (LiftedA l) (ps, ns, ls) = (ps, ns, l:ls)

-- | Execute negations
executeNegations :: RedexNeg rel => [NegAction rel] -> rel ()
executeNegations [] = pure ()
executeNegations (n:ns) = neg (naGoal n) Prelude.>> executeNegations ns

-- | Execute lifted actions
executeLifted :: Redex rel => [rel ()] -> rel ()
executeLifted [] = pure ()
executeLifted (a:as) = a Prelude.>> executeLifted as
