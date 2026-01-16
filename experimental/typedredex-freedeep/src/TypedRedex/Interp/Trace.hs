-- | Trace interpreter: execute queries with derivation trees.
module TypedRedex.Interp.Trace
  ( Derivation(..)
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
  , renderNeq
  , schedulePremisesChecked
  , translateRuleClosed
  )
import TypedRedex.Backend.Query (Query(..))
import TypedRedex.Backend.Goal
  ( Goal(..)
  , Subst(..)
  , emptySubst
  , exec
  , applySubstLogic
  )
import TypedRedex.Core.IxFree (IxFree(..))
import TypedRedex.Core.RuleF
import TypedRedex.Pretty

--------------------------------------------------------------------------------
-- Derivation Trees
--------------------------------------------------------------------------------

data DerivConclusion = DerivConclusion
  { dcName   :: String
  , dcFormat :: Maybe ([Doc] -> Doc)
  , dcArgs   :: [PrettyTerm]
  }

data Derivation = Derivation
  { derivRule        :: String
  , derivConclusion  :: DerivConclusion
  , derivPremises    :: [Derivation]
  , derivConstraints :: [Constraint]
  }

prettyDerivation :: Derivation -> String
prettyDerivation d =
  let (lines', _) = runPrettyWith emptyPrettyCtx (renderDeriv d)
  in unlines lines'
  where
    renderDeriv :: Derivation -> PrettyM [String]
    renderDeriv (Derivation rule concl prems constraints) = do
      conclDoc <- renderConclusion concl
      constraintDocs <- mapM renderConstraint constraints
      let concLine = renderDoc conclDoc
          constraintText =
            case constraintDocs of
              [] -> ""
              cs -> " [" ++ intercalate ", " (map renderDoc cs) ++ "]"
      case prems of
        [] -> do
          let line = replicate (length concLine) '-' ++ " [" ++ rule ++ "]" ++ constraintText
          pure [line, concLine]
        _ -> do
          premBlocks <- mapM renderDeriv prems
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
renderConstraint (NegC name) =
  pure (Doc "not(" <> Doc name <> Doc ")")

--------------------------------------------------------------------------------
-- Trace Execution
--------------------------------------------------------------------------------

trace :: Query a -> [(a, Derivation)]
trace q =
  let startSubst = emptySubst { substNextVar = queryNextVar q }
  in case queryCall q of
       SomeJudgmentCall jc ->
         [ (val, deriv)
         | (s, deriv) <- traceJudgmentCall jc startSubst
         , Just val <- [queryExtract q s]
         ]

traceJudgmentCall
  :: JudgmentCall name modes ts
  -> Subst
  -> [(Subst, Derivation)]
traceJudgmentCall jc s =
  concatMap (\rule -> traceRule jc rule s) (jcRules jc)

--------------------------------------------------------------------------------
-- Rule collection
--------------------------------------------------------------------------------

data CollectState = CollectState
  { csAvailVars :: Set Int
  , csPrems     :: [PremAction]
  , csNegs      :: [NegAction]
  , csHeadGoal  :: Maybe Goal
  }

emptyCollect :: CollectState
emptyCollect = CollectState S.empty [] [] Nothing

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
    collectRule caller (k term) st

  ConclF jc ->
    let (caller', headGoal) = resolveHead caller jc
        st' = st { csAvailVars = jcReqVars jc, csHeadGoal = Just headGoal }
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
        action = PremAction vars S.empty (PremConstraint constraint (Unify (termVal t1) (termVal t2))) (renderEq t1 t2)
        st' = st { csPrems = action : csPrems st }
    in collectRule caller (k ()) st'

  NEqF t1 t2 ->
    let vars = S.union (termVars t1) (termVars t2)
        constraint = NeqC (termVal t1) (termVal t2)
        action = PremAction vars S.empty (PremConstraint constraint (Disunify (termVal t1) (termVal t2))) (renderNeq t1 t2)
        st' = st { csPrems = action : csPrems st }
    in collectRule caller (k ()) st'
  where
    freshTerm :: forall a'. (Repr a', Typeable a') => State Subst (Term a')
    freshTerm = do
      s <- get
      let i = substNextVar s
      put s { substNextVar = i + 1 }
      pure (Term (S.singleton i) (Var i))

resolveHead
  :: Maybe (SomeTermList ts)
  -> JudgmentCall name modes ts
  -> (Maybe (SomeTermList ts), Goal)
resolveHead caller jc =
  case caller of
    Nothing ->
      (Just (SomeTermList (jcArgs jc)), Success)
    Just (SomeTermList args) ->
      (caller, unifyTermLists (jcArgs jc) args)

unifyTermLists :: TermList ts -> TermList ts -> Goal
unifyTermLists TNil TNil = Success
unifyTermLists (x :> xs) (y :> ys) =
  Conj (Unify (termVal x) (termVal y)) (unifyTermLists xs ys)

--------------------------------------------------------------------------------
-- Rule execution with trace
--------------------------------------------------------------------------------

traceRule
  :: JudgmentCall name modes ts
  -> Rule name ts
  -> Subst
  -> [(Subst, Derivation)]
traceRule jc (Rule ruleLabel body) s0 =
  let (collect, s1) = runState (collectRule (Just (SomeTermList (jcArgs jc))) body emptyCollect) s0
  in case csHeadGoal collect of
       Nothing -> []
       Just headGoal ->
         case schedulePremisesChecked ruleLabel (Just (SomeJudgmentCall jc)) (csAvailVars collect) (reverse (csPrems collect)) of
           Left err -> error err
           Right orderedPrems ->
             [ (sFinal, deriv)
             | sHead <- exec headGoal s1
             , (sPrem, premDerivs, premConstraints) <- runPremises orderedPrems sHead
             , (sFinal, negConstraints) <- runNegations (reverse (csNegs collect)) sPrem
             , let concl = buildConclusion jc sFinal
                   constraints = map (applySubstConstraint sFinal) (premConstraints ++ negConstraints)
                   deriv = Derivation ruleLabel concl premDerivs constraints
             ]

runPremises
  :: [PremAction]
  -> Subst
  -> [(Subst, [Derivation], [Constraint])]
runPremises [] s = [(s, [], [])]
runPremises (prem:rest) s =
  case paKind prem of
    PremCall jc ->
      [ (s'', deriv : ds, cs)
      | (s', deriv) <- traceJudgmentCall jc s
      , (s'', ds, cs) <- runPremises rest s'
      ]
    PremConstraint constraint goal ->
      [ (s'', ds, constraint : cs)
      | s' <- exec goal s
      , (s'', ds, cs) <- runPremises rest s'
      ]

runNegations :: [NegAction] -> Subst -> [(Subst, [Constraint])]
runNegations [] s = [(s, [])]
runNegations (NegAction goal label : rest) s =
  [ (s'', NegC label : cs)
  | s' <- exec (Neg goal) s
  , (s'', cs) <- runNegations rest s'
  ]

--------------------------------------------------------------------------------
-- Rendering helpers
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Substitution helpers
--------------------------------------------------------------------------------

applySubstConstraint :: Subst -> Constraint -> Constraint
applySubstConstraint s (EqC t1 t2) = EqC (applySubstLogic s t1) (applySubstLogic s t2)
applySubstConstraint s (NeqC t1 t2) = NeqC (applySubstLogic s t1) (applySubstLogic s t2)
applySubstConstraint _ (NegC name) = NegC name

applySubstPrettyTerm :: Subst -> PrettyTerm -> PrettyTerm
applySubstPrettyTerm s (PrettyTerm l) = PrettyTerm (applySubstLogic s l)

buildConclusion :: JudgmentCall name modes ts -> Subst -> DerivConclusion
buildConclusion jc s =
  DerivConclusion
    { dcName = jcName jc
    , dcFormat = jcFormat jc
    , dcArgs = map (applySubstPrettyTerm s) (jcPretty jc)
    }
