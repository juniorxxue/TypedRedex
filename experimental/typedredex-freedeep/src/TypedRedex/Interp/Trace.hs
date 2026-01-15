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

import TypedRedex.Backend.Eval
  ( Query(..)
  , SomeJudgmentCall(..)
  , translateRuleClosed
  )
import TypedRedex.Backend.Goal
  ( Goal(..)
  , Subst(..)
  , emptySubst
  , exec
  , applySubstLogic
  )
import TypedRedex.Core.IxFree (IxFree(..))
import TypedRedex.Core.RuleF hiding (Goal)

--------------------------------------------------------------------------------
-- Derivation Trees
--------------------------------------------------------------------------------

data Derivation = Derivation
  { derivRule        :: String
  , derivConclusion  :: String
  , derivPremises    :: [Derivation]
  , derivConstraints :: [String]
  } deriving (Eq, Show)

prettyDerivation :: Derivation -> String
prettyDerivation d = unlines (renderDeriv d)
  where
    renderDeriv :: Derivation -> [String]
    renderDeriv (Derivation rule concl prems constraints) =
      let concLine = concl
          constraintText =
            case constraints of
              [] -> ""
              cs -> " [" ++ intercalate ", " cs ++ "]"
      in case prems of
           [] ->
             let line = replicate (length concLine) '-' ++ " [" ++ rule ++ "]" ++ constraintText
             in [line, concLine]
           _ ->
             let premBlocks = map renderDeriv prems
                 combined = foldr1 sideBySide premBlocks
                 width = maximum (length concLine : map length combined)
                 line = replicate width '-' ++ " [" ++ rule ++ "]" ++ constraintText
                 concPad = (width - length concLine) `div` 2
                 concLine' = replicate concPad ' ' ++ concLine
             in combined ++ [line, concLine']

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
  :: JudgmentCall name modes vss ts
  -> Subst
  -> [(Subst, Derivation)]
traceJudgmentCall jc s =
  concatMap (\rule -> traceRule jc rule s) (jcRules jc)

--------------------------------------------------------------------------------
-- Rule collection
--------------------------------------------------------------------------------

data Constraint where
  EqC  :: (Repr a, Typeable a) => Logic a -> Logic a -> Constraint
  NeqC :: (Repr a, Typeable a) => Logic a -> Logic a -> Constraint
  NegC :: String -> Constraint

data PremKind where
  PremCall       :: JudgmentCall name modes vss ts -> PremKind
  PremConstraint :: Constraint -> Goal -> PremKind

data PremAction = PremAction
  { paReq  :: Set Int
  , paProd :: Set Int
  , paKind :: PremKind
  }

data NegAction = NegAction Goal String

data CollectState = CollectState
  { csAvailVars :: Set Int
  , csPrems     :: [PremAction]
  , csNegs      :: [NegAction]
  , csHeadGoal  :: Maybe Goal
  }

emptyCollect :: CollectState
emptyCollect = CollectState S.empty [] [] Nothing

data SomeTermList ts where
  SomeTermList :: TermList vss ts -> SomeTermList ts

collectRule
  :: forall ts s t a.
     Maybe (SomeTermList ts)
  -> IxFree (RuleF ts) s t a
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
    let action = PremAction (jcReqVars jc) (jcProdVars jc) (PremCall jc)
        st' = st { csPrems = action : csPrems st }
    in collectRule caller (k ()) st'

  NegF innerRule ->
    let action = NegAction (translateRuleClosed innerRule) (ruleName innerRule)
        st' = st { csNegs = action : csNegs st }
    in collectRule caller (k ()) st'

  EqF t1 t2 ->
    let vars = S.union (termVars t1) (termVars t2)
        constraint = EqC (termVal t1) (termVal t2)
        action = PremAction vars S.empty (PremConstraint constraint (Unify (termVal t1) (termVal t2)))
        st' = st { csPrems = action : csPrems st }
    in collectRule caller (k ()) st'

  NEqF t1 t2 ->
    let vars = S.union (termVars t1) (termVars t2)
        constraint = NeqC (termVal t1) (termVal t2)
        action = PremAction vars S.empty (PremConstraint constraint (Disunify (termVal t1) (termVal t2)))
        st' = st { csPrems = action : csPrems st }
    in collectRule caller (k ()) st'
  where
    freshTerm :: forall n a'. (Repr a', Typeable a') => State Subst (Term '[n] a')
    freshTerm = do
      s <- get
      let i = substNextVar s
      put s { substNextVar = i + 1 }
      pure (Term (S.singleton i) (Var i))

resolveHead
  :: Maybe (SomeTermList ts)
  -> JudgmentCall name modes vss ts
  -> (Maybe (SomeTermList ts), Goal)
resolveHead caller jc =
  case caller of
    Nothing ->
      (Just (SomeTermList (jcArgs jc)), Success)
    Just (SomeTermList args) ->
      (caller, unifyTermLists (jcArgs jc) args)

unifyTermLists :: TermList vss1 ts -> TermList vss2 ts -> Goal
unifyTermLists TNil TNil = Success
unifyTermLists (x :> xs) (y :> ys) =
  Conj (Unify (termVal x) (termVal y)) (unifyTermLists xs ys)

--------------------------------------------------------------------------------
-- Rule execution with trace
--------------------------------------------------------------------------------

traceRule
  :: JudgmentCall name modes vss ts
  -> Rule name ts
  -> Subst
  -> [(Subst, Derivation)]
traceRule jc (Rule ruleLabel body) s0 =
  let (collect, s1) = runState (collectRule (Just (SomeTermList (jcArgs jc))) body emptyCollect) s0
  in case csHeadGoal collect of
       Nothing -> []
       Just headGoal ->
         [ (sFinal, deriv)
         | sHead <- exec headGoal s1
         , (sPrem, premDerivs, premConstraints) <- runPremises (csAvailVars collect) (reverse (csPrems collect)) sHead
         , (sFinal, negConstraints) <- runNegations (reverse (csNegs collect)) sPrem
         , let concl = renderConclusion jc sFinal
               constraints = premConstraints ++ negConstraints
               deriv = Derivation ruleLabel concl premDerivs constraints
         ]

runPremises
  :: Set Int
  -> [PremAction]
  -> Subst
  -> [(Subst, [Derivation], [String])]
runPremises _ [] s = [(s, [], [])]
runPremises avail prems s =
  case selectReady avail prems of
    Nothing -> []
    Just (prem, rest) ->
      case paKind prem of
        PremCall jc ->
          [ (s'', deriv : ds, cs)
          | (s', deriv) <- traceJudgmentCall jc s
          , (s'', ds, cs) <- runPremises (S.union avail (paProd prem)) rest s'
          ]
        PremConstraint constraint goal ->
          [ (s'', ds, renderConstraint s' constraint : cs)
          | s' <- exec goal s
          , (s'', ds, cs) <- runPremises (S.union avail (paProd prem)) rest s'
          ]

runNegations :: [NegAction] -> Subst -> [(Subst, [String])]
runNegations [] s = [(s, [])]
runNegations (NegAction goal label : rest) s =
  [ (s'', renderConstraint s' (NegC label) : cs)
  | s' <- exec (Neg goal) s
  , (s'', cs) <- runNegations rest s'
  ]

selectReady :: Set Int -> [PremAction] -> Maybe (PremAction, [PremAction])
selectReady _ [] = Nothing
selectReady avail (p:ps)
  | paReq p `S.isSubsetOf` avail = Just (p, ps)
  | otherwise = case selectReady avail ps of
      Nothing -> Nothing
      Just (ready, rest) -> Just (ready, p : rest)

--------------------------------------------------------------------------------
-- Rendering helpers
--------------------------------------------------------------------------------

renderConclusion :: JudgmentCall name modes vss ts -> Subst -> String
renderConclusion jc s =
  let args = renderTermList s (jcArgs jc)
  in case args of
       [] -> jcName jc
       _  -> jcName jc ++ "(" ++ intercalate ", " args ++ ")"

renderTermList :: Subst -> TermList vss ts -> [String]
renderTermList _ TNil = []
renderTermList s (t :> ts) = renderTerm s t : renderTermList s ts

renderTerm :: (Repr a, Typeable a) => Subst -> Term vs a -> String
renderTerm s (Term _ l) = displayLogic (applySubstLogic s l)

renderConstraint :: Subst -> Constraint -> String
renderConstraint s (EqC t1 t2) =
  renderLogic s t1 ++ " = " ++ renderLogic s t2
renderConstraint s (NeqC t1 t2) =
  renderLogic s t1 ++ " =/= " ++ renderLogic s t2
renderConstraint _ (NegC name) =
  "not(" ++ name ++ ")"

renderLogic :: Repr a => Subst -> Logic a -> String
renderLogic s l = displayLogic (applySubstLogic s l)
