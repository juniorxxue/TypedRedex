{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Mode-check interpreter: analyze rules without executing them.
module TypedRedex.Interp.MCheck
  ( mcheck
  ) where

import Control.Monad.State.Strict (State, evalState, get, put)
import Data.List (intercalate)
import Data.Set (Set)
import qualified Data.Set as S

import TypedRedex.Core.IxFree (IxFree(..))
import TypedRedex.Core.RuleF
import TypedRedex.Nominal (FreshName(..))
import TypedRedex.Render

--------------------------------------------------------------------------------
-- Main interface
--------------------------------------------------------------------------------

class MCheck f where
  mcheckWith :: Int -> f -> String

instance MCheck (JudgmentCall name modes ts) where
  mcheckWith _ = mcheckCall

instance MCheck f => MCheck (Term a -> f) where
  mcheckWith i f = mcheckWith (i + 1) (f (var i))

-- | Analyze a judgment (recursively) and report mode warnings.
mcheck :: MCheck f => f -> String
mcheck = mcheckWith 0

mcheckCall :: JudgmentCall name modes ts -> String
mcheckCall jc =
  let warnings = evalState (checkJudgment jc) S.empty
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
  , exPrems     :: [CheckPrem]
  , exCalls     :: [SomeJudgmentCall]
  , exNegRules  :: [SomeRule]
  , exHeadCall  :: Maybe SomeJudgmentCall
  , exNextVar   :: Int
  , exNextName  :: Int
  }

emptyExtracted :: Extracted
emptyExtracted = Extracted S.empty [] [] [] Nothing 0 0

checkJudgment :: JudgmentCall name modes ts -> State (Set String) [String]
checkJudgment jc = do
  visited <- get
  if jcName jc `S.member` visited
    then pure []
    else do
      put (S.insert (jcName jc) visited)
      let reports = map (checkRule (jcName jc)) (jcRules jc)
          warnings = concatMap fst reports
          calls = concatMap snd reports
      nested <- fmap concat (mapM (\(SomeJudgmentCall cj) -> checkJudgment cj) calls)
      pure (warnings ++ nested)

checkRule :: String -> Rule name ts -> ([String], [SomeJudgmentCall])
checkRule judgmentName rule =
  checkRuleWithLabel judgmentName (ruleName rule) rule

checkRuleWithLabel :: String -> String -> Rule name ts -> ([String], [SomeJudgmentCall])
checkRuleWithLabel judgmentName label (Rule _ body) =
  let ex = extractRule body
      report = schedulePremisesReport (exAvailVars ex) (exPrems ex)
      ghostOut = ghostOutputs (exHeadCall ex) (exPrems ex)
      modeWarnings =
        case srBlocked report of
          Nothing | S.null ghostOut -> []
          _ -> [renderModeWarning judgmentName label (exHeadCall ex) (srBlocked report) ghostOut]
      orderWarnings =
        map (renderOrderWarning judgmentName label (exHeadCall ex)) (srAmbiguities report)
      negReports = map (checkNegRule judgmentName label) (exNegRules ex)
      negWarnings = concatMap fst negReports
      negCalls = concatMap snd negReports
  in (modeWarnings ++ orderWarnings ++ negWarnings, exCalls ex ++ negCalls)

checkNegRule :: String -> String -> SomeRule -> ([String], [SomeJudgmentCall])
checkNegRule judgmentName outerLabel (SomeRule rule) =
  let label = outerLabel ++ " / not " ++ ruleName rule
  in checkRuleWithLabel judgmentName label rule

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
  go body emptyExtracted
  where
    go :: RuleM ts a -> Extracted -> Extracted
    go (Pure _) ex = ex
    go (Bind op k) ex = case op of
      FreshF ->
        let varId = exNextVar ex
            -- Fresh introduces an unground logic variable; it does not make the
            -- variable "available" for mode scheduling.
            ex' = ex { exNextVar = varId + 1 }
            dummyTerm = Term (S.singleton varId) (Var varId)
        in go (k dummyTerm) ex'

      FreshNameF ->
        let nameId = exNextName ex
            name = freshName nameId
            ex' = ex { exNextName = nameId + 1 }
            dummyTerm = Term S.empty (Ground (project name))
        in go (k dummyTerm) ex'

      ConclF jc ->
        let ex' = ex
              { exHeadCall = Just (SomeJudgmentCall jc)
              , exAvailVars = S.union (exAvailVars ex) (jcReqVars jc)
              }
        in go (k ()) ex'

      PremF jc ->
        let prem = CheckPrem (jcReqVars jc) (jcProdVars jc) (renderJudgmentCall jc)
            ex' = ex
              { exPrems = exPrems ex ++ [prem]
              , exCalls = exCalls ex ++ [SomeJudgmentCall jc]
              }
        in go (k ()) ex'

      NegF innerRule ->
        let ex' = ex { exNegRules = exNegRules ex ++ [SomeRule innerRule] }
        in go (k ()) ex'

      EqF t1 t2 ->
        let vars = S.union (termVars t1) (termVars t2)
            prem = CheckPrem vars S.empty (renderEq t1 t2)
            ex' = ex { exPrems = exPrems ex ++ [prem] }
        in go (k ()) ex'

      NEqF t1 t2 ->
        let vars = S.union (termVars t1) (termVars t2)
            prem = CheckPrem vars S.empty (renderNeq t1 t2)
            ex' = ex { exPrems = exPrems ex ++ [prem] }
        in go (k ()) ex'

      HashF name term ->
        let vars = S.union (termVars name) (termVars term)
            prem = CheckPrem vars S.empty (renderHash name term)
            ex' = ex { exPrems = exPrems ex ++ [prem] }
        in go (k ()) ex'
