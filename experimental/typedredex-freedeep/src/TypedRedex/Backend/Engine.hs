-- | Shared evaluation engine: mode checks, scheduling, and goal translation.
module TypedRedex.Backend.Engine
  ( SomeJudgmentCall(..)
  , Constraint(..)
  , PremKind(..)
  , PremAction(..)
  , NegAction(..)
  , translate
  , translateRuleClosed
  , checkQueryInputs
  , schedulePremisesChecked
  , renderJudgmentCall
  , renderEq
  , renderNeq
  , renderHash
  ) where

import Data.List (intercalate)
import Data.Set (Set)
import qualified Data.Set as S

import TypedRedex.Backend.Goal
  ( Goal(..)
  , VarId(..)
  , logicVar
  )
import TypedRedex.Core.IxFree (IxFree(..))
import TypedRedex.Core.RuleF
import TypedRedex.Pretty (Doc(..), Pretty(..), formatJudgment)

-- | Existential wrapper for judgment calls.
data SomeJudgmentCall where
  SomeJudgmentCall :: JudgmentCall name modes ts -> SomeJudgmentCall

--------------------------------------------------------------------------------
-- Constraints and premises
--------------------------------------------------------------------------------

data Constraint where
  EqC  :: Pretty a => Logic a -> Logic a -> Constraint
  NeqC :: Pretty a => Logic a -> Logic a -> Constraint
  HashC :: (Pretty name, Pretty term) => Logic name -> Logic term -> Constraint
  NegC :: String -> Constraint

data PremKind where
  PremCall       :: JudgmentCall name modes ts -> PremKind
  PremConstraint :: Constraint -> Goal -> PremKind

data PremAction = PremAction
  { paReq  :: Set Int
  , paProd :: Set Int
  , paKind :: PremKind
  , paDesc :: String
  }

data NegAction = NegAction
  { naGoal  :: Goal
  , naLabel :: String
  }

--------------------------------------------------------------------------------
-- Translation to Goal
--------------------------------------------------------------------------------

data SomeTermList ts where
  SomeTermList :: TermList ts -> SomeTermList ts

-- | Translate a judgment call to a Goal.
translate :: JudgmentCall name modes ts -> Goal
translate jc =
  disjGoals [translateRule (Just (SomeTermList (jcArgs jc))) rule | rule <- jcRules jc]

translateRule :: Maybe (SomeTermList ts) -> Rule name ts -> Goal
translateRule caller (Rule name body) =
  buildGoal caller body (emptyState name)

-- | Translate a rule without external caller arguments (used for negation).
translateRuleClosed :: Rule name ts -> Goal
translateRuleClosed = translateRule Nothing

data DeferredAction
  = PremA PremAction
  | NegA NegAction

data InterpState = InterpState
  { isAvailVars :: Set Int
  , isDeferred  :: [DeferredAction]
  , isHeadGoal  :: Maybe Goal
  , isHeadCall  :: Maybe SomeJudgmentCall
  , isRuleName  :: String
  }

emptyState :: String -> InterpState
emptyState name = InterpState S.empty [] Nothing Nothing name

buildGoal :: forall ts a.
             Maybe (SomeTermList ts)
          -> RuleM ts a
          -> InterpState
          -> Goal
buildGoal _ (Pure _) st = finalize st
buildGoal caller (Bind op k) st = case op of

  FreshF ->
    Fresh $ \v ->
      let term = Term (S.singleton (unVarId v)) (logicVar v)
          st' = st { isAvailVars = S.insert (unVarId v) (isAvailVars st) }
      in buildGoal caller (k term) st'

  FreshNameF ->
    FreshName $ \name ->
      let term = Term S.empty name
      in buildGoal caller (k term) st

  ConclF jc ->
    let (caller', headGoal) = resolveHead caller jc
        st' = st
          { isAvailVars = S.union (isAvailVars st) (jcReqVars jc)
          , isHeadGoal = Just headGoal
          , isHeadCall = Just (SomeJudgmentCall jc)
          }
    in buildGoal caller' (k ()) st'

  PremF jc ->
    let action = PremA $ PremAction (jcReqVars jc) (jcProdVars jc) (PremCall jc) (renderJudgmentCall jc)
        st' = st { isDeferred = action : isDeferred st }
    in buildGoal caller (k ()) st'

  NegF innerRule ->
    let action = NegA (NegAction (translateRule Nothing innerRule) (ruleName innerRule))
        st' = st { isDeferred = action : isDeferred st }
    in buildGoal caller (k ()) st'

  EqF t1 t2 ->
    let vars = S.union (termVars t1) (termVars t2)
        constraint = EqC (termVal t1) (termVal t2)
        action = PremA $ PremAction vars S.empty (PremConstraint constraint (Unify (termVal t1) (termVal t2))) (renderEq t1 t2)
        st' = st { isDeferred = action : isDeferred st }
    in buildGoal caller (k ()) st'

  NEqF t1 t2 ->
    let vars = S.union (termVars t1) (termVars t2)
        constraint = NeqC (termVal t1) (termVal t2)
        action = PremA $ PremAction vars S.empty (PremConstraint constraint (Disunify (termVal t1) (termVal t2))) (renderNeq t1 t2)
        st' = st { isDeferred = action : isDeferred st }
    in buildGoal caller (k ()) st'

  HashF name term ->
    let vars = S.union (termVars name) (termVars term)
        constraint = HashC (termVal name) (termVal term)
        action = PremA $ PremAction vars S.empty (PremConstraint constraint (Hash (termVal name) (termVal term))) (renderHash name term)
        st' = st { isDeferred = action : isDeferred st }
    in buildGoal caller (k ()) st'

resolveHead :: Maybe (SomeTermList ts)
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

finalize :: InterpState -> Goal
finalize st =
  case isHeadGoal st of
    Nothing -> Failure
    Just headGoal ->
      let deferred = reverse (isDeferred st)
          (prems, negs) = partitionDeferred deferred
          negGoal = conjGoals (map (Neg . naGoal) negs)
      in case schedulePremisesChecked (isRuleName st) (isHeadCall st) (isAvailVars st) prems of
           Left err -> error err
           Right ordered ->
             let premGoal = conjGoals (map premToGoal ordered)
             in conjGoals [headGoal, premGoal, negGoal]
  where
    premToGoal :: PremAction -> Goal
    premToGoal prem =
      case paKind prem of
        PremCall jc -> translate jc
        PremConstraint _ goal -> goal

partitionDeferred :: [DeferredAction] -> ([PremAction], [NegAction])
partitionDeferred = foldr go ([], [])
  where
    go (PremA p) (ps, ns) = (p:ps, ns)
    go (NegA n) (ps, ns) = (ps, n:ns)

schedulePremisesChecked
  :: String
  -> Maybe SomeJudgmentCall
  -> Set Int
  -> [PremAction]
  -> Either String [PremAction]
schedulePremisesChecked ruleName headCall avail prems =
  let premSchedule = schedulePremises avail prems
      ghostOut = ghostOutputs headCall prems
      schedErr = either Just (const Nothing) premSchedule
  in if S.null ghostOut
       then case premSchedule of
              Left err -> Left (renderModeError ruleName headCall (Just err) ghostOut)
              Right ordered -> Right ordered
       else Left (renderModeError ruleName headCall schedErr ghostOut)

schedulePremises :: Set Int -> [PremAction] -> Either String [PremAction]
schedulePremises _ [] = Right []
schedulePremises avail prems =
  case selectReady avail prems of
    Nothing -> Left (renderScheduleError avail prems)
    Just (ready, rest) ->
      (ready :) <$> schedulePremises (S.union avail (paProd ready)) rest

selectReady :: Set Int -> [PremAction] -> Maybe (PremAction, [PremAction])
selectReady _ [] = Nothing
selectReady avail (p:ps)
  | paReq p `S.isSubsetOf` avail = Just (p, ps)
  | otherwise = case selectReady avail ps of
      Nothing -> Nothing
      Just (ready, rest) -> Just (ready, p : rest)

conjGoals :: [Goal] -> Goal
conjGoals = foldr Conj Success

disjGoals :: [Goal] -> Goal
disjGoals [] = Failure
disjGoals [g] = g
disjGoals (g:gs) = Disj g (disjGoals gs)

unVarId :: VarId a -> Int
unVarId (VarId i) = i

renderModeError
  :: String
  -> Maybe SomeJudgmentCall
  -> Maybe String
  -> Set Int
  -> String
renderModeError ruleName headCall schedErr ghostOut =
  intercalate "\n" (filter (not . null)
    [ "Mode error in rule " ++ ruleName
    , case headCall of
        Nothing -> ""
        Just (SomeJudgmentCall jc) -> "  conclusion: " ++ renderJudgmentCall jc
    , maybe "" id schedErr
    , if S.null ghostOut
        then ""
        else "  ghost outputs (never produced): " ++ renderVarSet ghostOut
    ])

renderJudgmentCall :: JudgmentCall name modes ts -> String
renderJudgmentCall jc =
  let docs = renderTermDocs (jcArgs jc)
      Doc rendered = formatJudgment (jcName jc) (jcFormat jc) docs
  in rendered

renderTerm :: Repr a => Term a -> String
renderTerm t =
  displayLogic (termVal t)

renderEq :: Repr a => Term a -> Term a -> String
renderEq t1 t2 = renderTerm t1 ++ " === " ++ renderTerm t2

renderNeq :: Repr a => Term a -> Term a -> String
renderNeq t1 t2 = renderTerm t1 ++ " =/= " ++ renderTerm t2

renderHash :: (Repr name, Repr term) => Term name -> Term term -> String
renderHash name term = renderTerm name ++ " # " ++ renderTerm term

renderVarSet :: Set Int -> String
renderVarSet s =
  case S.toAscList s of
    [] -> "(none)"
    xs -> intercalate " " (map renderVar xs)
  where
    renderVar i = "?" ++ show i

renderTermDocs :: TermList ts -> [Doc]
renderTermDocs TNil = []
renderTermDocs (t :> ts) = Doc (displayLogic (termVal t)) : renderTermDocs ts

renderScheduleError :: Set Int -> [PremAction] -> String
renderScheduleError avail prems =
  let blockedPrems = filter (\p -> not (paReq p `S.isSubsetOf` avail)) prems
      reqs = S.unions (map paReq blockedPrems)
      blocked = S.difference reqs avail
      prod = S.unions (map paProd prems)
      ghostInputs = S.difference blocked prod
      blockedMsg = "  blocked vars: " ++ renderVarSet blocked
      ghostMsg =
        if S.null ghostInputs
          then ""
          else "  ghost inputs (never produced): " ++ renderVarSet ghostInputs
      premLines = case blockedPrems of
        [] -> ""
        _ ->
          "  blocked premises:\n" ++ unlines (map (\p -> "    - " ++ paDesc p) blockedPrems)
  in intercalate "\n" (filter (not . null)
       [ "  cannot schedule premises"
       , blockedMsg
       , ghostMsg
       , premLines
       ])

ghostOutputs :: Maybe SomeJudgmentCall -> [PremAction] -> Set Int
ghostOutputs Nothing _ = S.empty
ghostOutputs (Just (SomeJudgmentCall jc)) prems =
  let bodyProd = S.unions (map paProd prems)
  in S.difference (jcProdVars jc) (S.union (jcReqVars jc) bodyProd)

checkQueryInputs :: JudgmentCall name modes ts -> Maybe String
checkQueryInputs jc =
  let inputVars' = jcReqVars jc
  in if S.null inputVars'
       then Nothing
       else Just (intercalate "\n"
         [ "Mode error in query"
         , "  call: " ++ renderJudgmentCall jc
         , "  ungrounded vars: " ++ renderVarSet inputVars'
         ])
