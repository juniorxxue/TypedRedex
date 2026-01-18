-- | Trace interpreter: execute queries with derivation trees.
module TypedRedex.Interp.Trace
  ( Derivation(..)
  , DerivStatus(..)
  , Failure(..)
  , PremTrace(..)
  , TraceResult(..)
  , prettyDerivation
  , trace
  ) where

import Control.Monad.State.Strict (State, get, put, runState)
import Data.List (intercalate)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Typeable (Typeable)

import TypedRedex.Backend.Engine
  ( SomeJudgmentCall(..)
  , Constraint(..)
  , PremKind(..)
  , PremAction(..)
  , NegAction(..)
  , renderEq
  , renderJudgmentCall
  , renderHash
  , renderNeq
  , schedulePremisesChecked
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
import TypedRedex.Pretty
import TypedRedex.Nominal (NominalAtom, FreshName(..))

--------------------------------------------------------------------------------
-- Derivation Trees
--------------------------------------------------------------------------------

data DerivConclusion = DerivConclusion
  { dcName   :: String
  , dcFormat :: Maybe ([Doc] -> Doc)
  , dcArgs   :: [PrettyTerm]
  }

data DerivStatus
  = Proven
  | Failed Failure

data PremTrace
  = PremDeriv Derivation
  | PremSkipped String
  | PremFailure Failure

data Failure
  = FailMode String
  | FailHead String
  | FailPremise String
  | FailConstraint String
  | FailNegation String

data Derivation = Derivation
  { derivRule        :: String
  , derivConclusion  :: DerivConclusion
  , derivPremises    :: [PremTrace]
  , derivConstraints :: [Constraint]
  , derivStatus      :: DerivStatus
  }

data TraceResult a
  = TraceOk a Derivation
  | TraceFail Failure Derivation

prettyDerivation :: Derivation -> String
prettyDerivation d =
  let (lines', _) = runPrettyWith emptyPrettyCtx (renderDeriv d)
  in unlines lines'
  where
    renderDeriv :: Derivation -> PrettyM [String]
    renderDeriv (Derivation rule concl prems constraints status) = do
      conclDoc <- renderConclusion concl
      constraintDocs <- mapM renderConstraint constraints
      let concLine = renderDoc conclDoc
          prems' =
            case status of
              Proven -> prems
              Failed failure -> prems ++ [PremFailure failure]
          constraintText =
            case constraintDocs of
              [] -> ""
              cs -> " [" ++ intercalate ", " (map renderDoc cs) ++ "]"
      case prems' of
        [] -> do
          let line = replicate (length concLine) '-' ++ " [" ++ rule ++ "]" ++ constraintText
          pure [line, concLine]
        _ -> do
          premBlocks <- mapM renderPremTrace prems'
          let combined = foldr1 sideBySide premBlocks
              width = maximum (length concLine : map length combined)
              line = replicate width '-' ++ " [" ++ rule ++ "]" ++ constraintText
              concPad = (width - length concLine) `div` 2
              concLine' = replicate concPad ' ' ++ concLine
          pure (combined ++ [line, concLine'])

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

    renderPremTrace :: PremTrace -> PrettyM [String]
    renderPremTrace (PremDeriv deriv) = renderDeriv deriv
    renderPremTrace (PremSkipped desc) = pure [desc ++ " (skipped)"]
    renderPremTrace (PremFailure failure) = pure ["[FAIL: " ++ failureSummary failure ++ "]"]

renderConclusion :: DerivConclusion -> PrettyM Doc
renderConclusion (DerivConclusion name fmt args) = do
  docs <- mapM renderPrettyTerm args
  pure (formatJudgment name fmt docs)

renderPrettyTerm :: PrettyTerm -> PrettyM Doc
renderPrettyTerm = prettyTermDoc

renderConstraint :: Constraint -> PrettyM Doc
renderConstraint (EqC t1 t2) = do
  d1 <- prettyLogic t1
  d2 <- prettyLogic t2
  pure (d1 <+> Doc " = " <+> d2)
renderConstraint (NeqC t1 t2) = do
  d1 <- prettyLogic t1
  d2 <- prettyLogic t2
  pure (d1 <+> Doc " =/= " <+> d2)
renderConstraint (HashC name term) = do
  d1 <- prettyLogic name
  d2 <- prettyLogic term
  pure (d1 <+> Doc " # " <+> d2)
renderConstraint (NegC name) =
  pure (Doc "not(" <> Doc name <> Doc ")")

failureSummary :: Failure -> String
failureSummary failure =
  case failure of
    FailMode msg -> takeWhile (/= '\n') msg
    FailHead msg -> "head failed: " ++ msg
    FailPremise msg -> "premise failed: " ++ msg
    FailConstraint msg -> "constraint failed: " ++ msg
    FailNegation msg -> "negation failed: " ++ msg

--------------------------------------------------------------------------------
-- Search tree
--------------------------------------------------------------------------------

data Search a
  = Fail Failure Derivation
  | Success a
  | Choice [Search a]

collectSuccesses :: Search a -> [a]
collectSuccesses (Fail _ _) = []
collectSuccesses (Success a) = [a]
collectSuccesses (Choice xs) = concatMap collectSuccesses xs

leftmostFailure :: Search a -> Maybe (Failure, Derivation)
leftmostFailure (Fail failure deriv) = Just (failure, deriv)
leftmostFailure (Success _) = Nothing
leftmostFailure (Choice xs) = go xs
  where
    go [] = Nothing
    go (x:rest) =
      case leftmostFailure x of
        Just res -> Just res
        Nothing -> go rest

--------------------------------------------------------------------------------
-- Trace Execution
--------------------------------------------------------------------------------

trace :: Query a -> [TraceResult a]
trace q =
  let startSubst = emptySubst { substNextVar = queryNextVar q }
  in case queryCall q of
       SomeJudgmentCall jc ->
         let search = searchJudgmentCall jc startSubst
             oks =
               [ TraceOk val deriv
               | (s, deriv) <- collectSuccesses search
               , Just val <- [queryExtract q s]
               ]
         in if null oks
              then case leftmostFailure search of
                     Just (failure, deriv) -> [TraceFail failure deriv]
                     Nothing -> []
              else oks

--------------------------------------------------------------------------------
-- Rule collection
--------------------------------------------------------------------------------

data CollectState = CollectState
  { csAvailVars :: Set Int
  , csPrems     :: [PremAction]
  , csNegs      :: [NegAction]
  , csHeadGoal  :: Maybe Goal
  , csHeadCall  :: Maybe SomeJudgmentCall
  }

emptyCollect :: CollectState
emptyCollect = CollectState S.empty [] [] Nothing Nothing

data SomeTermList ts where
  SomeTermList :: TermList ts -> SomeTermList ts

collectRule
  :: forall ts a.
     Maybe (SomeTermList ts)
  -> RuleM ts a
  -> CollectState
  -> State Subst CollectState
collectRule _ (Pure _) st = pure st
collectRule caller (Bind op k) st = case op of
  FreshF -> do
    term <- freshTerm
    let Term vars _ = term
        st' = st { csAvailVars = S.union (csAvailVars st) vars }
    collectRule caller (k term) st'

  FreshNameF -> do
    term <- freshNameTerm
    collectRule caller (k term) st

  ConclF jc ->
    let (caller', headGoal) = resolveHead caller jc
        st' = st
          { csAvailVars = S.union (csAvailVars st) (jcReqVars jc)
          , csHeadGoal = Just headGoal
          , csHeadCall = Just (SomeJudgmentCall jc)
          }
    in collectRule caller' (k ()) st'

  PremF jc ->
    let action = PremAction (jcReqVars jc) (jcProdVars jc) (PremCall jc) (renderJudgmentCall jc)
        st' = st { csPrems = action : csPrems st }
    in collectRule caller (k ()) st'

  NegF innerRule ->
    let action = NegAction (translateRuleClosed innerRule) (ruleName innerRule)
        st' = st { csNegs = action : csNegs st }
    in collectRule caller (k ()) st'

  EqF t1 t2 ->
    let vars = S.union (termVars t1) (termVars t2)
        constraint = EqC (termVal t1) (termVal t2)
        action = PremAction vars S.empty (PremConstraint constraint (G.Unify (termVal t1) (termVal t2))) (renderEq t1 t2)
        st' = st { csPrems = action : csPrems st }
    in collectRule caller (k ()) st'

  NEqF t1 t2 ->
    let vars = S.union (termVars t1) (termVars t2)
        constraint = NeqC (termVal t1) (termVal t2)
        action = PremAction vars S.empty (PremConstraint constraint (G.Disunify (termVal t1) (termVal t2))) (renderNeq t1 t2)
        st' = st { csPrems = action : csPrems st }
    in collectRule caller (k ()) st'

  HashF name term ->
    let vars = S.union (termVars name) (termVars term)
        constraint = HashC (termVal name) (termVal term)
        action = PremAction vars S.empty (PremConstraint constraint (G.Hash (termVal name) (termVal term))) (renderHash name term)
        st' = st { csPrems = action : csPrems st }
    in collectRule caller (k ()) st'
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

--------------------------------------------------------------------------------
-- Rule execution with trace
--------------------------------------------------------------------------------

searchJudgmentCall
  :: JudgmentCall name modes ts
  -> Subst
  -> Search (Subst, Derivation)
searchJudgmentCall jc s =
  case jcRules jc of
    [] ->
      let failure = FailHead (renderJudgmentCall jc)
          deriv = buildDerivation "<no rule>" jc s [] [] (Failed failure)
      in Fail failure deriv
    rules ->
      Choice [searchRule jc rule s | rule <- rules]

searchRule
  :: JudgmentCall name modes ts
  -> Rule name ts
  -> Subst
  -> Search (Subst, Derivation)
searchRule jc (Rule ruleLabel body) s0 =
  let (collect, s1) = runState (collectRule (Just (SomeTermList (jcArgs jc))) body emptyCollect) s0
  in case csHeadGoal collect of
       Nothing ->
         let failure = FailHead (renderJudgmentCall jc)
             deriv = buildDerivation ruleLabel jc s1 [] [] (Failed failure)
         in Fail failure deriv
       Just headGoal ->
         case schedulePremisesChecked ruleLabel (csHeadCall collect) (csAvailVars collect) (reverse (csPrems collect)) of
           Left err ->
             let failure = FailMode err
                 deriv = buildDerivation ruleLabel jc s1 [] [] (Failed failure)
             in Fail failure deriv
           Right orderedPrems ->
             case exec headGoal s1 of
               [] ->
                 let failure = FailHead (renderJudgmentCall jc)
                     deriv = buildDerivation ruleLabel jc s1 [] [] (Failed failure)
                 in Fail failure deriv
               heads ->
                 Choice
                   [ searchPremises jc ruleLabel orderedPrems (reverse (csNegs collect)) [] [] sHead
                   | sHead <- heads
                   ]

searchPremises
  :: JudgmentCall name modes ts
  -> String
  -> [PremAction]
  -> [NegAction]
  -> [PremTrace]
  -> [Constraint]
  -> Subst
  -> Search (Subst, Derivation)
searchPremises jc ruleLabel prems negs premTraces constraints s =
  case prems of
    [] ->
      searchNegations jc ruleLabel negs premTraces constraints s
    prem:rest ->
      case paKind prem of
        PremConstraint constraint goal ->
          case exec goal s of
            [] ->
              let constraints' = constraint : constraints
                  skipped = premTraces ++ skipPremises rest
                  failure = FailConstraint (paDesc prem)
                  deriv = buildDerivation ruleLabel jc s skipped constraints' (Failed failure)
              in Fail failure deriv
            subs ->
              Choice
                [ searchPremises jc ruleLabel rest negs premTraces (constraint : constraints) s'
                | s' <- subs
                ]
        PremCall call ->
          let branch = searchJudgmentCall call s
          in handlePremiseCall jc ruleLabel prem rest negs premTraces constraints s branch

handlePremiseCall
  :: JudgmentCall name modes ts
  -> String
  -> PremAction
  -> [PremAction]
  -> [NegAction]
  -> [PremTrace]
  -> [Constraint]
  -> Subst
  -> Search (Subst, Derivation)
  -> Search (Subst, Derivation)
handlePremiseCall jc ruleLabel prem rest negs premTraces constraints s branch =
  case branch of
    Fail _failure premDeriv ->
      let skipped = premTraces ++ [PremDeriv premDeriv] ++ skipPremises rest
          failure' = FailPremise (paDesc prem)
          deriv = buildDerivation ruleLabel jc s skipped constraints (Failed failure')
      in Fail failure' deriv
    Success (s', premDeriv) ->
      searchPremises jc ruleLabel rest negs (premTraces ++ [PremDeriv premDeriv]) constraints s'
    Choice branches ->
      Choice (map (handlePremiseCall jc ruleLabel prem rest negs premTraces constraints s) branches)

searchNegations
  :: JudgmentCall name modes ts
  -> String
  -> [NegAction]
  -> [PremTrace]
  -> [Constraint]
  -> Subst
  -> Search (Subst, Derivation)
searchNegations jc ruleLabel negs premTraces constraints s =
  case negs of
    [] ->
      let deriv = buildDerivation ruleLabel jc s premTraces constraints Proven
      in Success (s, deriv)
    NegAction goal label : rest ->
      case exec (G.Neg goal) s of
        [] ->
          let failure = FailNegation label
              deriv = buildDerivation ruleLabel jc s premTraces constraints (Failed failure)
          in Fail failure deriv
        subs ->
          Choice
            [ searchNegations jc ruleLabel rest premTraces (NegC label : constraints) s'
            | s' <- subs
            ]

skipPremises :: [PremAction] -> [PremTrace]
skipPremises = map (PremSkipped . paDesc)

--------------------------------------------------------------------------------
-- Rendering helpers
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Substitution helpers
--------------------------------------------------------------------------------

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
