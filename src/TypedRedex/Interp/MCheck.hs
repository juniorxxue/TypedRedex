{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Mode-check interpreter: analyze rules without executing them.
module TypedRedex.Interp.MCheck
  ( mcheck
  , mcheckVerbose
  ) where

import Control.Monad.State.Strict (State, evalState, get, put)
import Data.List (foldl', intercalate)
import Data.Set (Set)
import qualified Data.Set as S

import TypedRedex.Core.IxFree (IxFree(..))
import TypedRedex.Core.RuleF
import TypedRedex.Nominal (FreshName(..))
import TypedRedex.Render

--------------------------------------------------------------------------------
-- Main interface
--------------------------------------------------------------------------------

-- | Options for mode checking
data MCheckOpts = MCheckOpts
  { showOrderWarnings :: Bool  -- ^ Whether to show order warnings (default: False)
  }

defaultOpts :: MCheckOpts
defaultOpts = MCheckOpts { showOrderWarnings = False }

verboseOpts :: MCheckOpts
verboseOpts = MCheckOpts { showOrderWarnings = True }

class MCheck f where
  mcheckWith :: MCheckOpts -> Int -> f -> String

instance MCheck (JudgmentCall name modes ts) where
  mcheckWith opts _ = mcheckCall opts

instance MCheck f => MCheck (Term a -> f) where
  mcheckWith opts i f = mcheckWith opts (i + 1) (f (var i))

-- | Analyze a judgment (recursively) and report mode warnings.
-- Order warnings are hidden by default.
mcheck :: MCheck f => f -> String
mcheck = mcheckWith defaultOpts 0

-- | Analyze a judgment with verbose output, including order warnings.
mcheckVerbose :: MCheck f => f -> String
mcheckVerbose = mcheckWith verboseOpts 0

mcheckCall :: MCheckOpts -> JudgmentCall name modes ts -> String
mcheckCall opts jc =
  let warnings = evalState (checkJudgment opts jc) S.empty
  in if null warnings
       then "No mode warnings."
       else intercalate "\n\n" warnings

--------------------------------------------------------------------------------
-- Warning rendering
--------------------------------------------------------------------------------

renderModeWarning
  :: String
  -> String
  -> Maybe SomeJudgmentCall
  -> Maybe ScheduleBlocked
  -> Set Int
  -> String
renderModeWarning judgmentName ruleLabel headCall schedBlocked ghostOut =
  intercalate "\n" (filter (not . null)
    [ "Mode warning in judgment " ++ judgmentName ++ ", rule " ++ ruleLabel
    , case headCall of
        Nothing -> ""
        Just (SomeJudgmentCall jc) -> "  conclusion: " ++ renderJudgmentCall jc
    , maybe "" renderScheduleWarning schedBlocked
    , if S.null ghostOut
        then ""
        else "  ghost outputs (never produced): " ++ renderVarSet ghostOut
    ])

renderScheduleWarning :: ScheduleBlocked -> String
renderScheduleWarning blocked =
  let blockedMsg = "  blocked vars: " ++ renderVarSet (sbBlockedVars blocked)
      ghostMsg =
        if S.null (sbGhostInputs blocked)
          then ""
          else "  ghost inputs (never produced): " ++ renderVarSet (sbGhostInputs blocked)
      premLines =
        case sbBlockedPremises blocked of
          [] -> ""
          prems ->
            "  blocked premises:\n" ++ unlines (map (\p -> "    - " ++ p) prems)
  in intercalate "\n" (filter (not . null)
       [ "  cannot schedule premises"
       , blockedMsg
       , ghostMsg
       , premLines
       ])

renderOrderWarning
  :: String
  -> String
  -> Maybe SomeJudgmentCall
  -> ScheduleAmbiguity
  -> String
renderOrderWarning judgmentName ruleLabel headCall ambiguity =
  let choiceLines = unlines (map (\p -> "    - " ++ p) (saChoices ambiguity))
  in intercalate "\n" (filter (not . null)
       [ "Order warning in judgment " ++ judgmentName ++ ", rule " ++ ruleLabel
       , case headCall of
           Nothing -> ""
           Just (SomeJudgmentCall jc) -> "  conclusion: " ++ renderJudgmentCall jc
       , "  multiple ready premises (source order used):"
       , choiceLines
       ])

--------------------------------------------------------------------------------
-- Judgment checking
--------------------------------------------------------------------------------

data SomeJudgmentCall where
  SomeJudgmentCall :: JudgmentCall name modes ts -> SomeJudgmentCall

data SomeRule where
  SomeRule :: Rule name ts -> SomeRule

data CheckPrem = CheckPrem
  { cpReq  :: Set Int
  , cpProd :: Set Int
  , cpDesc :: String
  }

instance Schedulable CheckPrem where
  schedReqVars = cpReq
  schedProdVars = cpProd
  schedDesc = cpDesc

data Extracted = Extracted
  { exAvailVars :: Set Int
  , exGuards    :: [CheckPrem]
  , exPrems     :: [CheckPrem]
  , exCalls     :: [SomeJudgmentCall]
  , exNegRules  :: [SomeRule]
  , exHeadCall  :: Maybe SomeJudgmentCall
  , exNextVar   :: Int
  , exNextName  :: Int
  }

emptyExtracted :: Extracted
emptyExtracted = Extracted S.empty [] [] [] [] Nothing 0 0

checkJudgment :: MCheckOpts -> JudgmentCall name modes ts -> State (Set String) [String]
checkJudgment opts jc = do
  visited <- get
  if jcName jc `S.member` visited
    then pure []
    else do
      put (S.insert (jcName jc) visited)
      let reports = map (checkRule opts (jcName jc)) (jcRules jc)
          warnings = concatMap fst reports
          calls = concatMap snd reports
      nested <- fmap concat (mapM (\(SomeJudgmentCall cj) -> checkJudgment opts cj) calls)
      pure (warnings ++ nested)

checkRule :: MCheckOpts -> String -> Rule name ts -> ([String], [SomeJudgmentCall])
checkRule opts judgmentName rule =
  checkRuleWithLabel opts judgmentName (ruleName rule) rule

checkRuleWithLabel :: MCheckOpts -> String -> String -> Rule name ts -> ([String], [SomeJudgmentCall])
checkRuleWithLabel opts judgmentName label (Rule _ body) =
  let ex = extractRule body
      guards = exGuards ex
      avail' = foldr (S.union . cpProd) (exAvailVars ex) guards
      report = schedulePremisesReport avail' (exPrems ex)
      ghostOut = ghostOutputs (exHeadCall ex) (guards ++ exPrems ex)
      blocked =
        mergeBlocked
          (prefixBlocked "guard: " (checkGuardBlocked (exAvailVars ex) guards))
          (srBlocked report)
      modeWarnings =
        case blocked of
          Nothing | S.null ghostOut -> []
          _ -> [renderModeWarning judgmentName label (exHeadCall ex) blocked ghostOut]
      orderWarnings =
        if showOrderWarnings opts
          then map (renderOrderWarning judgmentName label (exHeadCall ex)) (srAmbiguities report)
          else []
      negReports = map (checkNegRule opts judgmentName label) (exNegRules ex)
      negWarnings = concatMap fst negReports
      negCalls = concatMap snd negReports
  in (modeWarnings ++ orderWarnings ++ negWarnings, exCalls ex ++ negCalls)

checkNegRule :: MCheckOpts -> String -> String -> SomeRule -> ([String], [SomeJudgmentCall])
checkNegRule opts judgmentName outerLabel (SomeRule rule) =
  let label = outerLabel ++ " / not " ++ ruleName rule
  in checkRuleWithLabel opts judgmentName label rule

ghostOutputs :: Maybe SomeJudgmentCall -> [CheckPrem] -> Set Int
ghostOutputs Nothing _ = S.empty
ghostOutputs (Just (SomeJudgmentCall jc)) prems =
  let bodyProd = S.unions (map cpProd prems)
  in S.difference (jcProdVars jc) (S.union (jcReqVars jc) bodyProd)

--------------------------------------------------------------------------------
-- Rule extraction
--------------------------------------------------------------------------------

extractRule :: RuleM ts a -> Extracted
extractRule body =
  go False body emptyExtracted
  where
    go :: Bool -> RuleM ts a -> Extracted -> Extracted
    go _ (Pure _) ex = ex
    go inGuard (Bind op k) ex = case op of
      FreshF ->
        let varId = exNextVar ex
            -- Fresh introduces an unground logic variable; it does not make the
            -- variable "available" for mode scheduling.
            ex' = ex { exNextVar = varId + 1 }
            dummyTerm = Term (S.singleton varId) (Var varId)
        in go inGuard (k dummyTerm) ex'

      FreshNameF ->
        let nameId = exNextName ex
            name = freshName nameId
            ex' = ex { exNextName = nameId + 1 }
            dummyTerm = Term S.empty (Ground (project name))
        in go inGuard (k dummyTerm) ex'

      GuardF innerRule ->
        let ex' = go True innerRule ex
        in go inGuard (k ()) ex'

      ConclF jc ->
        let ex' = ex
              { exHeadCall = Just (SomeJudgmentCall jc)
              , exAvailVars = S.union (exAvailVars ex) (jcReqVars jc)
              }
        in go inGuard (k ()) ex'

      PremF jc ->
        let prem = CheckPrem (jcReqVars jc) (jcProdVars jc) (renderJudgmentCall jc)
            ex' =
              if inGuard
                then ex
                  { exGuards = exGuards ex ++ [prem]
                  , exCalls = exCalls ex ++ [SomeJudgmentCall jc]
                  }
                else ex
                  { exPrems = exPrems ex ++ [prem]
                  , exCalls = exCalls ex ++ [SomeJudgmentCall jc]
                  }
        in go inGuard (k ()) ex'

      NegF innerRule ->
        let ex' = ex { exNegRules = exNegRules ex ++ [SomeRule innerRule] }
        in go inGuard (k ()) ex'

      EqF t1 t2 ->
        let vars = S.union (termVars t1) (termVars t2)
            prem = CheckPrem vars S.empty (renderEq t1 t2)
            ex' =
              if inGuard
                then ex { exGuards = exGuards ex ++ [prem] }
                else ex { exPrems = exPrems ex ++ [prem] }
        in go inGuard (k ()) ex'

      NEqF t1 t2 ->
        let vars = S.union (termVars t1) (termVars t2)
            prem = CheckPrem vars S.empty (renderNeq t1 t2)
            ex' =
              if inGuard
                then ex { exGuards = exGuards ex ++ [prem] }
                else ex { exPrems = exPrems ex ++ [prem] }
        in go inGuard (k ()) ex'

      HashF name term ->
        let vars = S.union (termVars name) (termVars term)
            prem = CheckPrem vars S.empty (renderHash name term)
            ex' =
              if inGuard
                then ex { exGuards = exGuards ex ++ [prem] }
                else ex { exPrems = exPrems ex ++ [prem] }
        in go inGuard (k ()) ex'

checkGuardBlocked :: Set Int -> [CheckPrem] -> Maybe ScheduleBlocked
checkGuardBlocked avail0 guards =
  let (_avail, missing, blockedDescs) =
        foldl' step (avail0, S.empty, []) guards
  in if null blockedDescs
       then Nothing
       else Just ScheduleBlocked
              { sbBlockedVars = missing
              , sbGhostInputs = S.empty
              , sbBlockedPremises = blockedDescs
              }
  where
    step (avail, missing, blockedDescs) p =
      let req = cpReq p
          missing' = if req `S.isSubsetOf` avail then missing else S.union missing (S.difference req avail)
          avail' = S.union avail (cpProd p)
          blockedDescs' = if req `S.isSubsetOf` avail then blockedDescs else blockedDescs ++ [cpDesc p]
      in (avail', missing', blockedDescs')

prefixBlocked :: String -> Maybe ScheduleBlocked -> Maybe ScheduleBlocked
prefixBlocked _ Nothing = Nothing
prefixBlocked prefix (Just b) =
  Just b { sbBlockedPremises = map (prefix ++) (sbBlockedPremises b) }

mergeBlocked :: Maybe ScheduleBlocked -> Maybe ScheduleBlocked -> Maybe ScheduleBlocked
mergeBlocked Nothing b = b
mergeBlocked a Nothing = a
mergeBlocked (Just a) (Just b) =
  Just ScheduleBlocked
    { sbBlockedVars = S.union (sbBlockedVars a) (sbBlockedVars b)
    , sbGhostInputs = S.union (sbGhostInputs a) (sbGhostInputs b)
    , sbBlockedPremises = sbBlockedPremises a ++ sbBlockedPremises b
    }
