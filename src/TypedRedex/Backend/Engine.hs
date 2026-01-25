-- | Shared evaluation engine: scheduling and goal translation.
module TypedRedex.Backend.Engine
  ( SomeJudgmentCall(..)
  , Constraint(..)
  , PremKind(..)
  , PremAction(..)
  , NegAction(..)
  , translate
  , translateRuleClosed
  ) where

import Data.List (foldl')
import Data.Set (Set)
import qualified Data.Set as S

import TypedRedex.Backend.Goal
  ( Goal(..)
  , VarId(..)
  , logicVar
  )
import TypedRedex.Core.IxFree (IxFree(..))
import TypedRedex.Core.RuleF
import TypedRedex.Pretty (Pretty(..))
import TypedRedex.Render (renderEq, renderJudgmentCall, renderHash, renderNeq)

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

instance Schedulable PremAction where
  schedReqVars = paReq
  schedProdVars = paProd
  schedDesc = paDesc

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
translateRule caller (Rule _ body) =
  buildGoal caller body emptyState

-- | Translate a rule without external caller arguments (used for negation).
translateRuleClosed :: Rule name ts -> Goal
translateRuleClosed = translateRule Nothing

data DeferredAction
  = PremA PremAction
  | NegA NegAction

data InterpState = InterpState
  { isAvailVars :: Set Int
  , isGuards   :: [PremAction]
  , isDeferred  :: [DeferredAction]
  , isHeadGoal  :: Maybe Goal
  }

emptyState :: InterpState
emptyState = InterpState S.empty [] [] Nothing

buildGoal :: forall ts a.
             Maybe (SomeTermList ts)
          -> RuleM ts a
          -> InterpState
          -> Goal
buildGoal caller m st =
  run False caller m st (\_ _ st' -> finalize st')
  where
    -- CPS interpreter so GuardF can run a nested program and then continue.
    run :: forall a'. Bool -> Maybe (SomeTermList ts) -> RuleM ts a' -> InterpState
        -> (a' -> Maybe (SomeTermList ts) -> InterpState -> Goal)
        -> Goal
    run _ caller' (Pure a) st' cont = cont a caller' st'
    run inGuard caller' (Bind op k) st' cont = case op of

      FreshF ->
        Fresh $ \v ->
          let term = Term (S.singleton (unVarId v)) (logicVar v)
          -- Fresh introduces an unground logic variable; it is not "available"
          -- for mode scheduling until it is produced by an output or provided
          -- by the caller via the rule head inputs.
          in run inGuard caller' (k term) st' cont

      FreshNameF ->
        FreshName $ \name ->
          let term = Term S.empty name
          in run inGuard caller' (k term) st' cont

      GuardF inner ->
        run True caller' inner st' (\_ caller'' st'' -> run inGuard caller'' (k ()) st'' cont)

      ConclF jc ->
        let (caller'', headGoal) = resolveHead caller' jc
            st'' = st'
              { isAvailVars = S.union (isAvailVars st') (jcReqVars jc)
              , isHeadGoal = Just headGoal
              }
        in run inGuard caller'' (k ()) st'' cont

      PremF jc ->
        let premAction = PremAction (jcReqVars jc) (jcProdVars jc) (PremCall jc) (renderJudgmentCall jc)
            st'' =
              if inGuard
                then st' { isGuards = premAction : isGuards st' }
                else st' { isDeferred = PremA premAction : isDeferred st' }
        in run inGuard caller' (k ()) st'' cont

      NegF innerRule ->
        let action = NegA (NegAction (translateRule Nothing innerRule) (ruleName innerRule))
            st'' = st' { isDeferred = action : isDeferred st' }
        in run inGuard caller' (k ()) st'' cont

      EqF t1 t2 ->
        let vars = S.union (termVars t1) (termVars t2)
            constraint = EqC (termVal t1) (termVal t2)
            premAction =
              PremAction vars S.empty (PremConstraint constraint (Unify (termVal t1) (termVal t2))) (renderEq t1 t2)
            st'' =
              if inGuard
                then st' { isGuards = premAction : isGuards st' }
                else st' { isDeferred = PremA premAction : isDeferred st' }
        in run inGuard caller' (k ()) st'' cont

      NEqF t1 t2 ->
        let vars = S.union (termVars t1) (termVars t2)
            constraint = NeqC (termVal t1) (termVal t2)
            premAction =
              PremAction vars S.empty (PremConstraint constraint (Disunify (termVal t1) (termVal t2))) (renderNeq t1 t2)
            st'' =
              if inGuard
                then st' { isGuards = premAction : isGuards st' }
                else st' { isDeferred = PremA premAction : isDeferred st' }
        in run inGuard caller' (k ()) st'' cont

      HashF name term ->
        let vars = S.union (termVars name) (termVars term)
            constraint = HashC (termVal name) (termVal term)
            premAction =
              PremAction vars S.empty (PremConstraint constraint (Hash (termVal name) (termVal term))) (renderHash name term)
            st'' =
              if inGuard
                then st' { isGuards = premAction : isGuards st' }
                else st' { isDeferred = PremA premAction : isDeferred st' }
        in run inGuard caller' (k ()) st'' cont

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
      let guards = reverse (isGuards st)
          deferred = reverse (isDeferred st)
          (prems, negs) = partitionDeferred deferred
          negGoal = conjGoals (map (Neg . naGoal) negs)
          avail' = foldl' (\a p -> S.union a (paProd p)) (isAvailVars st) guards
          ordered = guards ++ schedulePremises avail' prems
          premGoal = conjGoals (map premToGoal ordered)
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
conjGoals :: [Goal] -> Goal
conjGoals = foldr Conj Success

disjGoals :: [Goal] -> Goal
disjGoals [] = Failure
disjGoals [g] = g
disjGoals (g:gs) = Disj g (disjGoals gs)

unVarId :: VarId a -> Int
unVarId (VarId i) = i
