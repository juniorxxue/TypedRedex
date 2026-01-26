-- | Debug interpreter: execute queries while streaming rule-matching progress.
--
-- This mirrors the Trace interpreter's search structure, but emits messages to
-- stdout as it explores rules/premises. The primary goal is to help locate
-- where a search is "stuck" even when it does not terminate.
--
-- Features animated TUI output with colors:
-- - Yellow: currently trying a rule
-- - Green: successful match
-- - Red: failed match
-- - Progress-bar style: failed attempts are overwritten, only final result shown
module TypedRedex.Interp.Debug
  ( DebugOpts(..)
  , DebugResult(..)
  , defaultDebugOpts
  , debug
  , debugWith
  ) where

import Control.Concurrent (threadDelay)
import Control.Monad (when, forM_)
import Control.Monad.State.Strict (State, get, put, runState)
import Data.IORef
import Data.Maybe (isJust)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Typeable (Typeable)
import System.IO (hFlush, stdout)

import TypedRedex.Backend.Engine
  ( SomeJudgmentCall(..)
  , Constraint(..)
  , PremKind(..)
  , PremAction(..)
  , NegAction(..)
  , translateRuleClosed
  )
import TypedRedex.Backend.Query (Query(..))
import TypedRedex.Backend.Goal
  ( Goal
  , Subst(..)
  , emptySubst
  , exec
  , applySubstLogic
  )
import qualified TypedRedex.Backend.Goal as G
import TypedRedex.Core.IxFree (IxFree(..))
import TypedRedex.Core.RuleF
import TypedRedex.Interp.Trace
  ( DerivConclusion(..)
  , Derivation(..)
  , DerivStatus(..)
  , Failure(..)
  , PremTrace(..)
  , TraceResult(..)
  )
import TypedRedex.Nominal (NominalAtom, FreshName(..))
import TypedRedex.Pretty
  ( Doc(..)
  , PrettyM
  , PrettyTerm(..)
  , formatJudgment
  , maskedPrettyCtx
  , prettyLogic
  , prettyTermDoc
  , runPrettyWith
  , (<+>)
  )

--------------------------------------------------------------------------------
-- Public API
--------------------------------------------------------------------------------

-- | Result from debug interpreter (simplified, no derivation tree).
data DebugResult a
  = DebugOk a
  | DebugFail Failure

data DebugOpts = DebugOpts
  { dbgIndentSpaces :: Int
  -- ^ Spaces per nesting level.
  , dbgShowConstraints :: Bool
  -- ^ Whether to print constraint steps (Eq/Neq/Hash/Neg).
  , dbgOmitNames :: Set String
  -- ^ Rule labels or judgment names to suppress in the output.
  , dbgDelayMicros :: Int
  -- ^ Delay in microseconds after each output line (0 = no delay).
  -- Useful for step-by-step viewing.
  , dbgVerbose :: Bool
  -- ^ If True, show more detailed information about each step.
  , dbgAnimate :: Bool
  -- ^ If True, use animated output (overwrite failed attempts).
  , dbgColors :: Bool
  -- ^ If True, use ANSI colors in output.
  }

defaultDebugOpts :: DebugOpts
defaultDebugOpts = DebugOpts
  { dbgIndentSpaces = 2
  , dbgShowConstraints = False
  , dbgOmitNames = S.empty
  , dbgDelayMicros = 0
  , dbgVerbose = True
  , dbgAnimate = True
  , dbgColors = True
  }

-- | Run a query with streaming debug output (default options).
debug :: Query a -> IO [DebugResult a]
debug = debugWith defaultDebugOpts

-- | Run a query with streaming debug output.
--
-- Returns a simplified result without derivation trees.
debugWith :: DebugOpts -> Query a -> IO [DebugResult a]
debugWith opts q = do
  os <- newOutputState opts
  let startSubst = emptySubst { substNextVar = queryNextVar q }
  case queryCall q of
    SomeJudgmentCall jc -> do
      putDbgLine os 0 colorCyan ("Goal: " ++ renderJudgmentCallMasked startSubst jc)
      m <- pickJudgmentCallTop os (queryExtract q) 0 jc startSubst
      pure $ case m of
        Nothing -> []
        Just (TraceOk a _) -> [DebugOk a]
        Just (TraceFail failure _) -> [DebugFail failure]

--------------------------------------------------------------------------------
-- Debug printing with colors and animation
--------------------------------------------------------------------------------

-- ANSI color codes
colorReset, colorRed, colorGreen, colorYellow, colorCyan, colorDim :: String
colorReset  = "\ESC[0m"
colorRed    = "\ESC[31m"
colorGreen  = "\ESC[32m"
colorYellow = "\ESC[33m"
colorCyan   = "\ESC[36m"
colorDim    = "\ESC[2m"

-- ANSI cursor control
cursorUp :: Int -> String
cursorUp n = "\ESC[" ++ show n ++ "F"

clearLine :: String
clearLine = "\ESC[K"

-- | Output state for tracking lines for animation
data OutputState = OutputState
  { osLineCount :: IORef Int  -- ^ Lines printed at current depth that can be cleared
  , osOpts :: DebugOpts
  }

newOutputState :: DebugOpts -> IO OutputState
newOutputState opts = do
  lineRef <- newIORef 0
  pure OutputState
    { osLineCount = lineRef
    , osOpts = opts
    }

-- | Print a line with optional color
putColored :: DebugOpts -> String -> String -> IO ()
putColored opts color msg = do
  if dbgColors opts
    then putStr (color ++ msg ++ colorReset)
    else putStr msg

-- | Print with indentation and newline
putDbgLine :: OutputState -> Int -> String -> String -> IO ()
putDbgLine os depth color msg = do
  let opts = osOpts os
  putStr (replicate (dbgIndentSpaces opts * depth) ' ')
  putColored opts color msg
  putStrLn ""
  hFlush stdout
  modifyIORef' (osLineCount os) (+1)
  when (dbgDelayMicros opts > 0) $
    threadDelay (dbgDelayMicros opts)

-- | Print temporary line (for animation - will be cleared)
putDbgTemp :: OutputState -> Int -> String -> String -> IO ()
putDbgTemp os depth color msg = do
  let opts = osOpts os
  putStr (replicate (dbgIndentSpaces opts * depth) ' ')
  putColored opts color msg
  putStrLn ""
  hFlush stdout
  when (dbgDelayMicros opts > 0) $
    threadDelay (dbgDelayMicros opts)

-- | Clear N lines (move up and clear each)
clearLines :: OutputState -> Int -> IO ()
clearLines os n = do
  let opts = osOpts os
  when (dbgAnimate opts && n > 0) $ do
    putStr (cursorUp n)
    forM_ [1..n] $ \_ -> do
      putStr clearLine
      putStrLn ""
    putStr (cursorUp n)
    hFlush stdout

--------------------------------------------------------------------------------
-- Trace-like selection (but streaming)
--------------------------------------------------------------------------------

data PickResult a
  = PickOk a Derivation
  | PickFail Failure Derivation Int

data RuleOutcome a
  = RuleNoMatch
  -- ^ Head unification failed; this rule does not apply.
  | RuleRejected
  -- ^ Rule matched and proved, but the success was rejected by the accept predicate.
  | RulePicked (PickResult a)

pickJudgmentCallTop
  :: OutputState
  -> (Subst -> Maybe a)
  -> Int
  -> JudgmentCall name modes ts
  -> Subst
  -> IO (Maybe (TraceResult a))
pickJudgmentCallTop os extract depth jc s = do
  let opts = osOpts os
  mpick <- pickJudgmentCall (dbgOmitNames opts) (isJust . extract) os depth jc s
  pure $ case mpick of
    Nothing -> Nothing
    Just (PickOk s' deriv) ->
      case extract s' of
        Nothing -> Nothing
        Just a -> Just (TraceOk a deriv)
    Just (PickFail failure deriv _) ->
      Just (TraceFail failure deriv)

pickJudgmentCall
  :: forall name modes ts.
     Set String
  -> (Subst -> Bool)  -- ^ Whether to accept a successful substitution (top-level only).
  -> OutputState
  -> Int
  -> JudgmentCall name modes ts
  -> Subst
  -> IO (Maybe (PickResult Subst))
pickJudgmentCall omit accept os depth jc s =
  case jcRules jc of
    [] -> do
      let failure = FailHead (renderJudgmentCallMasked s jc)
          deriv = buildDerivation "<no rule>" jc s [] [] (Failed failure)
      pure (Just (PickFail failure deriv (derivDepth deriv)))
    rules -> do
      -- Explore rules left-to-right, keeping the first success and the deepest failure.
      go Nothing False 0 rules
  where
    go
      :: Maybe (PickResult Subst) -- best failure so far
      -> Bool                     -- saw any non-NoMatch branch
      -> Int                      -- lines printed for "no match" rules (to clear on success)
      -> [Rule name ts]
      -> IO (Maybe (PickResult Subst))
    go best sawNonNoMatch linesToClear rs =
      case rs of
        [] ->
          case best of
            Just _ -> pure best
            Nothing ->
              if sawNonNoMatch
                then pure Nothing
                else do
                  let failure = FailHead (renderJudgmentCallMasked s jc)
                      deriv = buildDerivation "<no matching rule>" jc s [] [] (Failed failure)
                  putDbgLine os depth colorRed ("✗ No matching rule for: " ++ renderJudgmentCallMasked s jc)
                  pure (Just (PickFail failure deriv (derivDepth deriv)))
        rule:rest -> do
          (outcome, linesAdded) <- pickRule omit accept os depth jc rule s linesToClear
          case outcome of
            RuleNoMatch ->
              go best sawNonNoMatch linesAdded rest
            RuleRejected ->
              go best True 0 rest  -- Reset line count after rejection
            RulePicked ok@(PickOk _ _) ->
              pure (Just ok)
            RulePicked failRes@(PickFail _ _ _) ->
              go (Just (bestFailure best failRes)) True 0 rest

    bestFailure :: Maybe (PickResult Subst) -> PickResult Subst -> PickResult Subst
    bestFailure Nothing cand = cand
    bestFailure (Just curr@(PickFail _ _ depthCurr)) cand@(PickFail _ _ depthCand)
      | depthCurr >= depthCand = curr
      | otherwise = cand
    -- Candidate is only ever a failure in this loop; keep this case to satisfy
    -- exhaustiveness checking.
    bestFailure (Just curr@(PickFail _ _ _)) (PickOk _ _) = curr
    bestFailure (Just ok@(PickOk _ _)) _ = ok

pickRule
  :: forall name modes ts.
     Set String
  -> (Subst -> Bool)
  -> OutputState
  -> Int
  -> JudgmentCall name modes ts
  -> Rule name ts
  -> Subst
  -> Int  -- ^ Lines already printed (for clearing)
  -> IO (RuleOutcome Subst, Int)  -- ^ Outcome and total lines printed
pickRule omit accept os depth jc (Rule ruleLabel body) s0 linesBefore = do
  if ruleLabel `S.member` (omit `S.union` dbgOmitNames (osOpts os)) || jcName jc `S.member` omit
    then pickRuleBody False accept os depth jc ruleLabel body s0 linesBefore
    else do
      pickRuleBody True accept os depth jc ruleLabel body s0 linesBefore
  where
    -- Rule evaluation with animation support
    pickRuleBody
      :: Bool
      -> (Subst -> Bool)
      -> OutputState
      -> Int
      -> JudgmentCall name modes ts
      -> String
      -> RuleM ts ()
      -> Subst
      -> Int
      -> IO (RuleOutcome Subst, Int)
    pickRuleBody showHeader accept' os' depth' jc' label' body' s0' linesBef = do
      let opts' = osOpts os'

      -- Clear previous "no match" lines if animating
      when (showHeader && dbgAnimate opts' && linesBef > 0) $
        clearLines os' linesBef

      when showHeader $
        putDbgTemp os' depth' colorYellow ("⋯ " ++ label')

      let (collect, s1) =
            runState (collectRule False (Just (SomeTermList (jcArgs jc'))) body' emptyCollect) s0'
      case csHeadGoal collect of
        Nothing -> do
          let failure = FailHead (renderJudgmentCallMasked s1 jc')
              deriv = buildDerivation label' jc' s1 [] [] (Failed failure)
          when showHeader $ do
            clearLines os' 1  -- Clear the "trying" line
            putDbgLine os' depth' colorRed ("✗ " ++ label' ++ " (head mismatch)")
          pure (RulePicked (PickFail failure deriv (derivDepth deriv)), 1)
        Just headGoal -> do
          let guards = reverse (csGuards collect)
              avail' = foldr (S.union . paProd) (csAvailVars collect) guards
              orderedPrems = guards ++ schedulePremises avail' (reverse (csPrems collect))
              negs = reverse (csNegs collect)
          case exec headGoal s1 of
            [] -> do
              -- No match - print dimmed and keep for animation
              when showHeader $ do
                clearLines os' 1  -- Clear the "trying" line
                putDbgLine os' depth' colorDim ("· " ++ label')
              pure (RuleNoMatch, 1)
            heads -> do
              -- Matched! Clear the "trying" line and show match
              when showHeader $ do
                clearLines os' 1
                putDbgLine os' depth' colorGreen ("▸ " ++ label')
                when (dbgVerbose opts' && not (null orderedPrems)) $ do
                  let premCount = length [() | pa <- orderedPrems, isPremCall (paKind pa)]
                  when (premCount > 0) $
                    putDbgLine os' depth' "" ("  " ++ show premCount ++ " premise(s):")
              picked <- pickChoices os' (map (pickPremises accept' os' depth' jc' label' 1 orderedPrems negs [] []) heads)
              case picked of
                Nothing -> do
                  when showHeader $
                    putDbgLine os' depth' colorYellow ("  ↩ " ++ label' ++ " rejected")
                  pure (RuleRejected, 0)
                Just p@(PickOk _ _) -> do
                  when showHeader $
                    putDbgLine os' depth' colorGreen ("  ✓ " ++ label' ++ " succeeded")
                  pure (RulePicked p, 0)
                Just p@(PickFail _ _ _) -> do
                  when showHeader $
                    putDbgLine os' depth' colorRed ("  ✗ " ++ label' ++ " premise failed")
                  pure (RulePicked p, 0)

    isPremCall (PremCall _) = True
    isPremCall _ = False

-- Pick the first success; otherwise the deepest failure.
pickChoices :: OutputState -> [IO (Maybe (PickResult Subst))] -> IO (Maybe (PickResult Subst))
pickChoices _os = go Nothing
  where
    go best [] = pure best
    go best (m:ms) = do
      r <- m
      case r of
        Nothing -> go best ms
        Just ok@(PickOk _ _) -> pure (Just ok)
        Just failRes@(PickFail _ _ _) ->
          go (Just (bestFailure best failRes)) ms

    bestFailure Nothing cand = cand
    bestFailure (Just curr@(PickFail _ _ depthCurr)) cand@(PickFail _ _ depthCand)
      | depthCurr >= depthCand = curr
      | otherwise = cand
    -- Candidate is only ever a failure in this loop; keep this case to satisfy
    -- exhaustiveness checking.
    bestFailure (Just curr@(PickFail _ _ _)) (PickOk _ _) = curr
    bestFailure (Just ok@(PickOk _ _)) _ = ok

pickPremises
  :: (Subst -> Bool)
  -> OutputState
  -> Int
  -> JudgmentCall name modes ts
  -> String
  -> Int
  -> [PremAction]
  -> [NegAction]
  -> [PremTrace]
  -> [Constraint]
  -> Subst
  -> IO (Maybe (PickResult Subst))
pickPremises accept os depth jc ruleLabel taskN prems negs premTraces constraints s =
  let opts = osOpts os
  in case prems of
    [] ->
      pickNegations accept os depth jc ruleLabel negs premTraces constraints s
    prem:rest ->
      case paKind prem of
        PremConstraint constraint goal -> do
          when (dbgShowConstraints opts) $
            putDbgLine os (depth + 2) colorDim ("  Constraint: " ++ renderConstraintMasked s constraint)
          case exec goal s of
            [] -> do
              when (dbgShowConstraints opts) $
                putDbgLine os (depth + 2) colorRed ("  ✗ Constraint failed")
              let constraints' = constraint : constraints
                  skipped = premTraces ++ skipPremises rest
                  failure = FailConstraint (renderConstraintMasked s constraint)
                  deriv = buildDerivation ruleLabel jc s skipped constraints' (Failed failure)
              pure (Just (PickFail failure deriv (derivDepth deriv)))
            subs ->
              pickChoices os
                [ pickPremises accept os depth jc ruleLabel taskN rest negs premTraces (constraint : constraints) s'
                | s' <- subs
                ]
        PremCall call -> do
          let totalPrems = taskN + length [() | pa <- prems, isPremCall (paKind pa)] - 1
          putDbgLine os (depth + 1) colorCyan ("  [" ++ show taskN ++ "/" ++ show totalPrems ++ "] " ++ renderJudgmentCallMasked s call)
          mcall <- pickJudgmentCall (dbgOmitNames opts) (const True) os (depth + 2) call s
          case mcall of
            Nothing -> do
              putDbgLine os (depth + 1) colorRed ("  ✗ Premise " ++ show taskN ++ " has no solution")
              let skipped = premTraces ++ skipPremises rest
                  failure = FailPremise (renderJudgmentCallMasked s call)
                  deriv = buildDerivation ruleLabel jc s skipped constraints (Failed failure)
              pure (Just (PickFail failure deriv (derivDepth deriv)))
            Just (PickFail _failure premDeriv _) -> do
              putDbgLine os (depth + 1) colorRed ("  ✗ Premise " ++ show taskN ++ " failed")
              let skipped = premTraces ++ [PremDeriv premDeriv] ++ skipPremises rest
                  failure = FailPremise (renderJudgmentCallMasked s call)
                  deriv = buildDerivation ruleLabel jc s skipped constraints (Failed failure)
              pure (Just (PickFail failure deriv (derivDepth deriv)))
            Just (PickOk s' premDeriv) -> do
              when (dbgVerbose opts) $
                putDbgLine os (depth + 1) colorGreen ("  ✓ Premise " ++ show taskN ++ " => " ++ renderJudgmentCallMasked s' call)
              pickPremises accept os depth jc ruleLabel (taskN + 1) rest negs (premTraces ++ [PremDeriv premDeriv]) constraints s'
  where
    isPremCall (PremCall _) = True
    isPremCall _ = False

pickNegations
  :: (Subst -> Bool)
  -> OutputState
  -> Int
  -> JudgmentCall name modes ts
  -> String
  -> [NegAction]
  -> [PremTrace]
  -> [Constraint]
  -> Subst
  -> IO (Maybe (PickResult Subst))
pickNegations accept os depth jc ruleLabel negs premTraces constraints s =
  let opts = osOpts os
  in case negs of
    [] -> do
      if accept s
        then do
          let deriv = buildDerivation ruleLabel jc s premTraces constraints Proven
          pure (Just (PickOk s deriv))
        else pure Nothing
    NegAction goal label : rest -> do
      when (dbgShowConstraints opts) $
        putDbgLine os (depth + 2) colorDim ("  Negation: not(" ++ label ++ ")")
      case exec (G.Neg goal) s of
        [] -> do
          when (dbgShowConstraints opts) $
            putDbgLine os (depth + 2) colorRed ("  ✗ Negation failed")
          let failure = FailNegation label
              deriv = buildDerivation ruleLabel jc s premTraces constraints (Failed failure)
          pure (Just (PickFail failure deriv (derivDepth deriv)))
        subs ->
          pickChoices os
            [ pickNegations accept os depth jc ruleLabel rest premTraces (NegC label : constraints) s'
            | s' <- subs
            ]

--------------------------------------------------------------------------------
-- Derivation helpers (copied from Trace interpreter)
--------------------------------------------------------------------------------

derivDepth :: Derivation -> Int
derivDepth deriv =
  1 + maximum (0 : [derivDepth d | PremDeriv d <- derivPremises deriv])

skipPremises :: [PremAction] -> [PremTrace]
skipPremises = map (PremSkipped . paDesc)

applySubstConstraint :: Subst -> Constraint -> Constraint
applySubstConstraint s (EqC t1 t2) = EqC (applySubstLogic s t1) (applySubstLogic s t2)
applySubstConstraint s (NeqC t1 t2) = NeqC (applySubstLogic s t1) (applySubstLogic s t2)
applySubstConstraint s (HashC name term) = HashC (applySubstLogic s name) (applySubstLogic s term)
applySubstConstraint _ (NegC name) = NegC name

applySubstPrettyTerm :: Subst -> PrettyTerm -> PrettyTerm
applySubstPrettyTerm s (PrettyTerm l) = PrettyTerm (applySubstLogic s l)

buildDerivation
  :: String
  -> JudgmentCall name modes ts
  -> Subst
  -> [PremTrace]
  -> [Constraint]
  -> DerivStatus
  -> Derivation
buildDerivation ruleLabel jc s prems constraints status =
  let concl = buildConclusion jc s
      applied = map (applySubstConstraint s) (reverse constraints)
  in Derivation
       { derivRule = ruleLabel
       , derivConclusion = concl
       , derivPremises = prems
       , derivConstraints = applied
       , derivStatus = status
       }

buildConclusion :: JudgmentCall name modes ts -> Subst -> DerivConclusion
buildConclusion jc s =
  DerivConclusion
    { dcName = jcName jc
    , dcFormat = jcFormat jc
    , dcArgs = map (applySubstPrettyTerm s) (jcPretty jc)
    }

--------------------------------------------------------------------------------
-- Rendering (masked vars + substitution applied)
--------------------------------------------------------------------------------

renderJudgmentCallMasked :: Subst -> JudgmentCall name modes ts -> String
renderJudgmentCallMasked s jc =
  let ((doc :: Doc), _) = runPrettyWith maskedPrettyCtx $ do
        docs <- mapM prettyTermDoc (map (applySubstPrettyTerm s) (jcPretty jc))
        pure (formatJudgment (jcName jc) (jcFormat jc) docs)
  in renderDoc doc

renderConstraintMasked :: Subst -> Constraint -> String
renderConstraintMasked s c =
  let ((doc :: Doc), _) = runPrettyWith maskedPrettyCtx (renderConstraint c)
  in renderDoc doc
  where
    renderConstraint :: Constraint -> PrettyM Doc
    renderConstraint (EqC t1 t2) = do
      d1 <- prettyLogic (applySubstLogic s t1)
      d2 <- prettyLogic (applySubstLogic s t2)
      pure (d1 <+> Doc " = " <+> d2)
    renderConstraint (NeqC t1 t2) = do
      d1 <- prettyLogic (applySubstLogic s t1)
      d2 <- prettyLogic (applySubstLogic s t2)
      pure (d1 <+> Doc " =/= " <+> d2)
    renderConstraint (HashC name term) = do
      d1 <- prettyLogic (applySubstLogic s name)
      d2 <- prettyLogic (applySubstLogic s term)
      pure (d1 <+> Doc " # " <+> d2)
    renderConstraint (NegC name) =
      pure (Doc "not(" <> Doc name <> Doc ")")

--------------------------------------------------------------------------------
-- Rule collection (copied from Trace interpreter)
--------------------------------------------------------------------------------

data CollectState = CollectState
  { csAvailVars :: Set Int
  , csGuards    :: [PremAction]
  , csPrems     :: [PremAction]
  , csNegs      :: [NegAction]
  , csHeadGoal  :: Maybe Goal
  , csHeadCall  :: Maybe SomeJudgmentCall
  }

emptyCollect :: CollectState
emptyCollect = CollectState S.empty [] [] [] Nothing Nothing

data SomeTermList ts where
  SomeTermList :: TermList ts -> SomeTermList ts

collectRule
  :: forall ts a.
     Bool
  -> Maybe (SomeTermList ts)
  -> RuleM ts a
  -> CollectState
  -> State Subst CollectState
collectRule _ _ (Pure _) st = pure st
collectRule inGuard caller (Bind op k) st = case op of
  FreshF -> do
    term <- freshTerm
    collectRule inGuard caller (k term) st

  FreshNameF -> do
    term <- freshNameTerm
    collectRule inGuard caller (k term) st

  GuardF innerRule -> do
    st' <- collectRule True caller innerRule st
    collectRule inGuard caller (k ()) st'

  ConclF jc ->
    let (caller', headGoal) = resolveHead caller jc
        st' = st
          { csAvailVars = S.union (csAvailVars st) (jcReqVars jc)
          , csHeadGoal = Just headGoal
          , csHeadCall = Just (SomeJudgmentCall jc)
          }
    in collectRule inGuard caller' (k ()) st'

  PremF jc -> do
    s <- get
    let desc = renderJudgmentCallMasked s jc
        action = PremAction (jcReqVars jc) (jcProdVars jc) (PremCall jc) desc
        st' =
          if inGuard
            then st { csGuards = action : csGuards st }
            else st { csPrems = action : csPrems st }
    collectRule inGuard caller (k ()) st'

  NegF innerRule ->
    let action = NegAction (translateRuleClosed innerRule) (ruleName innerRule)
        st' = st { csNegs = action : csNegs st }
    in collectRule inGuard caller (k ()) st'

  EqF t1 t2 -> do
    s <- get
    let vars = S.union (termVars t1) (termVars t2)
        constraint = EqC (termVal t1) (termVal t2)
        desc = renderConstraintMasked s constraint
        action =
          PremAction vars S.empty (PremConstraint constraint (G.Unify (termVal t1) (termVal t2))) desc
        st' =
          if inGuard
            then st { csGuards = action : csGuards st }
            else st { csPrems = action : csPrems st }
    collectRule inGuard caller (k ()) st'

  NEqF t1 t2 -> do
    s <- get
    let vars = S.union (termVars t1) (termVars t2)
        constraint = NeqC (termVal t1) (termVal t2)
        desc = renderConstraintMasked s constraint
        action =
          PremAction vars S.empty (PremConstraint constraint (G.Disunify (termVal t1) (termVal t2))) desc
        st' =
          if inGuard
            then st { csGuards = action : csGuards st }
            else st { csPrems = action : csPrems st }
    collectRule inGuard caller (k ()) st'

  HashF name term -> do
    s <- get
    let vars = S.union (termVars name) (termVars term)
        constraint = HashC (termVal name) (termVal term)
        desc = renderConstraintMasked s constraint
        action =
          PremAction vars S.empty (PremConstraint constraint (G.Hash (termVal name) (termVal term))) desc
        st' =
          if inGuard
            then st { csGuards = action : csGuards st }
            else st { csPrems = action : csPrems st }
    collectRule inGuard caller (k ()) st'
  where
    freshTerm :: forall a'. (Repr a', Typeable a') => State Subst (Term a')
    freshTerm = do
      s <- get
      let i = substNextVar s
      put s { substNextVar = i + 1 }
      pure (Term (S.singleton i) (Var i))

    freshNameTerm :: forall a'. (NominalAtom a', FreshName a', Repr a', Typeable a') => State Subst (Term a')
    freshNameTerm = do
      s <- get
      let i = substNextName s
          name = freshName i
      put s { substNextName = i + 1 }
      pure (Term S.empty (Ground (project name)))

resolveHead
  :: Maybe (SomeTermList ts)
  -> JudgmentCall name modes ts
  -> (Maybe (SomeTermList ts), Goal)
resolveHead caller jc =
  case caller of
    Nothing ->
      (Just (SomeTermList (jcArgs jc)), G.Success)
    Just (SomeTermList args) ->
      (caller, unifyTermLists (jcArgs jc) args)

unifyTermLists :: TermList ts -> TermList ts -> Goal
unifyTermLists TNil TNil = G.Success
unifyTermLists (x :> xs) (y :> ys) =
  G.Conj (G.Unify (termVal x) (termVal y)) (unifyTermLists xs ys)
