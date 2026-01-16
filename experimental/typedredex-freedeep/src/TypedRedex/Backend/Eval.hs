-- | Eval interpreter: execute queries via miniKanren
--
-- Translate rule ASTs into a Goal AST, then execute via the miniKanren backend.
module TypedRedex.Backend.Eval
  ( -- * Query execution
    eval
  , Query(..)
  , SomeJudgmentCall(..)
  , query
  , QueryM
  , qfresh
    -- * Translation
  , translate
  , translateRuleClosed
  ) where

import Control.Monad.State.Strict (State, evalState, get, put)
import Data.Kind (Type)
import Data.List (intercalate)
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Typeable (Typeable)

import TypedRedex.Backend.Goal
  ( Goal(..)
  , VarId(..)
  , Subst(..)
  , emptySubst
  , exec
  , applySubstLogic
  , logicVar
  )
import TypedRedex.Core.IxFree (IxFree(..))
import TypedRedex.Core.RuleF
import TypedRedex.Pretty (Doc(..), formatJudgment)

-- | A query to execute.
-- | Existential wrapper for judgment calls.
data SomeJudgmentCall where
  SomeJudgmentCall :: JudgmentCall name modes ts -> SomeJudgmentCall

-- | A query to execute.
data Query a = Query
  { queryGoal     :: Goal
  , queryNextVar  :: Int
  , queryExtract  :: Subst -> Maybe a
  , queryCall     :: SomeJudgmentCall
  }

-- | Evaluate a query.
eval :: Query a -> [a]
eval q =
  let startSubst = emptySubst { substNextVar = queryNextVar q }
  in mapMaybe (queryExtract q) (exec (queryGoal q) startSubst)

--------------------------------------------------------------------------------
-- Query builder
--------------------------------------------------------------------------------

-- | Query-building monad with fresh logic variables.
newtype QueryM a = QueryM (State Int a)
  deriving (Functor, Applicative, Monad)

-- | Allocate a fresh query variable.
qfresh :: forall a. (Repr a, Typeable a) => QueryM (Term a)
qfresh = QueryM $ do
  i <- get
  put (i + 1)
  pure (Term (S.singleton i) (Var i))

-- | Build a query from a judgment call and output spec.
query :: forall out name modes ts.
         (Extract out, CollectVars out)
      => QueryM (JudgmentCall name modes ts, out)
      -> Query (Out out)
query qm =
  let (result, nextVar) = runQueryState qm
      (jc, outSpec) = result
      varsInCall = varsTermList (jcArgs jc)
      varsInOut  = collectVars outSpec
      maxVar     = maxVarId (S.union varsInCall varsInOut)
      nextVar'   = max nextVar (maxVar + 1)
      goal       = translate jc
      extractFn  = \s -> extractOut s outSpec
  in case checkQueryInputs jc of
       Nothing ->
         Query
           { queryGoal = goal
           , queryNextVar = nextVar'
           , queryExtract = extractFn
           , queryCall = SomeJudgmentCall jc
           }
       Just err -> error err
  where
    runQueryState :: QueryM a -> (a, Int)
    runQueryState (QueryM st) = evalState ((,) <$> st <*> get) 0

--------------------------------------------------------------------------------
-- Output extraction
--------------------------------------------------------------------------------

class Extract a where
  type Out a :: Type
  extractOut :: Subst -> a -> Maybe (Out a)

instance (Repr a, Typeable a) => Extract (Term a) where
  type Out (Term a) = a
  extractOut s t = evalTerm s t

instance (Extract a, Extract b) => Extract (a, b) where
  type Out (a, b) = (Out a, Out b)
  extractOut s (a, b) = (,) <$> extractOut s a <*> extractOut s b

instance (Extract a, Extract b, Extract c) => Extract (a, b, c) where
  type Out (a, b, c) = (Out a, Out b, Out c)
  extractOut s (a, b, c) = (,,) <$> extractOut s a <*> extractOut s b <*> extractOut s c

instance (Extract a, Extract b, Extract c, Extract d) => Extract (a, b, c, d) where
  type Out (a, b, c, d) = (Out a, Out b, Out c, Out d)
  extractOut s (a, b, c, d) =
    (,,,) <$> extractOut s a <*> extractOut s b <*> extractOut s c <*> extractOut s d

instance (Extract a, Extract b, Extract c, Extract d, Extract e) => Extract (a, b, c, d, e) where
  type Out (a, b, c, d, e) = (Out a, Out b, Out c, Out d, Out e)
  extractOut s (a, b, c, d, e) =
    (,,,,) <$> extractOut s a <*> extractOut s b <*> extractOut s c <*> extractOut s d <*> extractOut s e

evalTerm :: (Repr a, Typeable a) => Subst -> Term a -> Maybe a
evalTerm s (Term _ l) =
  case applySubstLogic s l of
    Var _      -> Nothing
    Ground r -> reify r

--------------------------------------------------------------------------------
-- Variable collection helpers
--------------------------------------------------------------------------------

class CollectVars a where
  collectVars :: a -> Set Int

instance CollectVars (Term a) where
  collectVars = termVars

instance (CollectVars a, CollectVars b) => CollectVars (a, b) where
  collectVars (a, b) = S.union (collectVars a) (collectVars b)

instance (CollectVars a, CollectVars b, CollectVars c) => CollectVars (a, b, c) where
  collectVars (a, b, c) = S.unions [collectVars a, collectVars b, collectVars c]

instance (CollectVars a, CollectVars b, CollectVars c, CollectVars d) => CollectVars (a, b, c, d) where
  collectVars (a, b, c, d) = S.unions [collectVars a, collectVars b, collectVars c, collectVars d]

instance (CollectVars a, CollectVars b, CollectVars c, CollectVars d, CollectVars e) => CollectVars (a, b, c, d, e) where
  collectVars (a, b, c, d, e) =
    S.unions [collectVars a, collectVars b, collectVars c, collectVars d, collectVars e]

varsTermList :: TermList ts -> Set Int
varsTermList TNil = S.empty
varsTermList (t :> ts) = S.union (termVars t) (varsTermList ts)

maxVarId :: Set Int -> Int
maxVarId s
  | S.null s = -1
  | otherwise = S.foldl' max (-1) s

--------------------------------------------------------------------------------
-- Translation to Goal
--------------------------------------------------------------------------------

-- | Existential wrapper for term lists with any variable-set indices.
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
  | NegA Goal

data PremAction = PremAction
  { paReq  :: Set Int
  , paProd :: Set Int
  , paGoal :: Goal
  , paDesc :: String
  }

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
      in buildGoal caller (k term) st

  ConclF jc ->
    let (caller', headGoal) = resolveHead caller jc
        st' = st
          { isAvailVars = jcReqVars jc
          , isHeadGoal = Just headGoal
          , isHeadCall = Just (SomeJudgmentCall jc)
          }
    in buildGoal caller' (k ()) st'

  PremF jc ->
    let action = PremA $ PremAction (jcReqVars jc) (jcProdVars jc) (translate jc) (renderJudgmentCall jc)
        st' = st { isDeferred = action : isDeferred st }
    in buildGoal caller (k ()) st'

  NegF innerRule ->
    let action = NegA (translateRule Nothing innerRule)
        st' = st { isDeferred = action : isDeferred st }
    in buildGoal caller (k ()) st'

  EqF t1 t2 ->
    let vars = S.union (termVars t1) (termVars t2)
        action = PremA $ PremAction vars S.empty (Unify (termVal t1) (termVal t2)) (renderEq t1 t2)
        st' = st { isDeferred = action : isDeferred st }
    in buildGoal caller (k ()) st'

  NEqF t1 t2 ->
    let vars = S.union (termVars t1) (termVars t2)
        action = PremA $ PremAction vars S.empty (Disunify (termVal t1) (termVal t2)) (renderNeq t1 t2)
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
          premSchedule = schedulePremises (isAvailVars st) prems
          negGoal = conjGoals (map (Neg . extractNeg) negs)
          ghostOut = ghostOutputs (isHeadCall st) prems
          schedErr = either Just (const Nothing) premSchedule
      in if S.null ghostOut
           then case premSchedule of
                  Left err -> error (renderModeError (isRuleName st) (isHeadCall st) (Just err) ghostOut)
                  Right ordered ->
                    let premGoal = conjGoals (map paGoal ordered)
                    in conjGoals [headGoal, premGoal, negGoal]
           else error (renderModeError (isRuleName st) (isHeadCall st) schedErr ghostOut)
  where
    extractNeg (NegA g) = g
    extractNeg _ = Success

partitionDeferred :: [DeferredAction] -> ([PremAction], [DeferredAction])
partitionDeferred = foldr go ([], [])
  where
    go (PremA p) (ps, ns) = (p:ps, ns)
    go n@(NegA _) (ps, ns) = (ps, n:ns)

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
