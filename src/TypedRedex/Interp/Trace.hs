-- | Trace interpreter: execute queries with derivation trees.
module TypedRedex.Interp.Trace
  ( Derivation(..)
  , DerivStatus(..)
  , Failure(..)
  , PremTrace(..)
  , TraceResult(..)
  , prettyDerivation
  , prettyDerivationWithOmit
  , trace
  ) where

import Control.Monad.State.Strict (State, get, put, runState)
import Data.List (intercalate)
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Typeable (Typeable)

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
import TypedRedex.Pretty
import TypedRedex.Nominal (NominalAtom, FreshName(..))
import TypedRedex.Render (renderEq, renderHash, renderJudgmentCall, renderNeq)

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
prettyDerivation = prettyDerivationWithOmit []

prettyDerivationWithOmit :: [String] -> Derivation -> String
prettyDerivationWithOmit omitNames d =
  let omitSet = S.fromList omitNames
      (lines', _) = runPrettyWith emptyPrettyCtx (renderDeriv omitSet d)
  in unlines lines'
  where
    renderDeriv :: Set String -> Derivation -> PrettyM [String]
    renderDeriv omitSet (Derivation rule concl prems constraints status) = do
      conclDoc <- renderConclusion concl
      constraintDocs <- mapM renderConstraint constraints
      let concLine = renderDoc conclDoc
          filtered = mapMaybe (filterPremTrace omitSet) prems
          prems' = filtered
          constraintText =
            case constraintDocs of
              [] -> ""
              cs -> " [" ++ intercalate ", " (map renderDoc cs) ++ "]"
          failureText =
            case status of
              Proven -> ""
              Failed failure -> " [FAIL: " ++ failureSummary failure ++ "]"
          concLineFull = concLine ++ failureText
      case prems' of
        [] -> do
          let line = replicate (length concLineFull) '-' ++ " [" ++ rule ++ "]" ++ constraintText
          pure [line, concLineFull]
        _ -> do
          premBlocks <- mapM (renderPremTrace omitSet) prems'
          let combined = foldr1 sideBySide premBlocks
              width = maximum (length concLineFull : map length combined)
              line = replicate width '-' ++ " [" ++ rule ++ "]" ++ constraintText
              concPad = (width - length concLineFull) `div` 2
              concLine' = replicate concPad ' ' ++ concLineFull
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

    renderPremTrace :: Set String -> PremTrace -> PrettyM [String]
    renderPremTrace omitSet (PremDeriv deriv) = renderDeriv omitSet deriv
    renderPremTrace _ (PremSkipped desc) = pure [desc ++ " (skipped)"]
    renderPremTrace _ (PremFailure failure) = pure ["[FAIL: " ++ failureSummary failure ++ "]"]

    filterPremTrace :: Set String -> PremTrace -> Maybe PremTrace
    filterPremTrace omitSet prem =
      case prem of
        PremDeriv deriv ->
          if dcName (derivConclusion deriv) `S.member` omitSet
            || derivRule deriv `S.member` omitSet
            then Nothing
            else Just prem
        _ -> Just prem

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
  = NoMatch
  | Fail Failure Derivation
  | Success a
  | Choice [Search a]

--------------------------------------------------------------------------------
-- Trace Execution
--------------------------------------------------------------------------------

trace :: Query a -> [TraceResult a]
trace q =
  let startSubst = emptySubst { substNextVar = queryNextVar q }
  in case queryCall q of
       SomeJudgmentCall jc ->
         case selectTrace (queryExtract q) (searchJudgmentCall jc startSubst) of
           Just res -> [res]
           Nothing -> []

data PickResult a
  = PickOk a Derivation
  | PickFail Failure Derivation Int

selectTrace
  :: (Subst -> Maybe a)
  -> Search (Subst, Derivation)
  -> Maybe (TraceResult a)
selectTrace extract search =
  toTrace <$> select search
  where
    toTrace pick =
      case pick of
        PickOk a deriv -> TraceOk a deriv
        PickFail failure deriv _ -> TraceFail failure deriv

    select NoMatch = Nothing
    select (Fail failure deriv) =
      Just (PickFail failure deriv (derivDepth deriv))
    select (Success (s, deriv)) =
      case extract s of
        Just a -> Just (PickOk a deriv)
        Nothing -> Nothing
    select (Choice xs) = selectChoice xs

    selectChoice = go Nothing
      where
        go best [] = best
        go best (x:rest) =
          case select x of
            Nothing -> go best rest
            Just ok@(PickOk _ _) -> Just ok
            Just fail@(PickFail _ _ _) ->
              go (Just (bestFailure best fail)) rest

    bestFailure Nothing candidate = candidate
    bestFailure (Just current@(PickFail _ _ depthCurr)) candidate@(PickFail _ _ depthCand)
      | depthCurr >= depthCand = current
      | otherwise = candidate
    bestFailure (Just (PickOk _ _)) candidate = candidate

derivDepth :: Derivation -> Int
derivDepth deriv =
  1 + maximum (0 : [derivDepth d | PremDeriv d <- derivPremises deriv])

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
    -- Fresh introduces an unground logic variable; it is not "available" for
    -- mode scheduling until it is produced by an output or provided by the
    -- caller via the rule head inputs.
    collectRule caller (k term) st

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
      let branches = [searchRule jc rule s | rule <- rules]
          filtered = filter (not . isNoMatch) branches
      in case filtered of
           [] ->
             let failure = FailHead (renderJudgmentCall jc)
                 deriv = buildDerivation "<no matching rule>" jc s [] [] (Failed failure)
             in Fail failure deriv
           _ -> Choice filtered

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
         let orderedPrems = schedulePremises (csAvailVars collect) (reverse (csPrems collect))
         in case exec headGoal s1 of
              [] -> NoMatch
              heads ->
                Choice
                  [ searchPremises jc ruleLabel orderedPrems (reverse (csNegs collect)) [] [] sHead
                  | sHead <- heads
                  ]

isNoMatch :: Search a -> Bool
isNoMatch NoMatch = True
isNoMatch _ = False

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
    NoMatch ->
      let skipped = premTraces ++ skipPremises rest
          failure' = FailPremise (paDesc prem)
          deriv = buildDerivation ruleLabel jc s skipped constraints (Failed failure')
      in Fail failure' deriv
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
