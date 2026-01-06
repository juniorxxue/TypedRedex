{-# LANGUAGE TypeFamilies, Rank2Types, GeneralisedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs, ExistentialQuantification, ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Deterministic failure-aware tracing interpreter.
--
-- The standard tracing interpreter ("TypedRedex.Interp.Tracing") is implemented
-- as @StateT TracingState Stream@ to support *fair backtracking search*.
--
-- That design has an important trade-off: when a branch fails via 'empty',
-- the underlying 'Stream' has no value to carry, so the @StateT@ state for that
-- branch is discarded. In particular, the derivation stack is lost, which makes
-- it impossible (without redesigning the search representation) to reconstruct
-- a "partial derivation tree" for failed examples.
--
-- In practice, many TypedRedex users model *deterministic, syntax-directed*
-- systems (at most one successful derivation). For troubleshooting those
-- systems, it is often enough to produce a *single* informative failure trace:
-- follow alternatives left-to-right, and if everything fails, report the
-- deepest/most informative partial derivation encountered.
--
-- This module implements that strategy:
--   * still supports disjunction ('<|>') to try later rules when earlier ones fail
--   * but keeps only one "best failure" (by derivation depth; ties are left-biased)
--   * and, crucially, preserves partial derivation trees on failure by carrying
--     a failure value instead of dropping the entire branch state like 'Stream' does.
--
-- This is intentionally *not* a full "failed search tree" feature for arbitrary
-- nondeterministic programs; it is a focused, lower-complexity debugging tool.
module TypedRedex.Interp.Tracing.Deterministic
  ( -- * Running with failure traces
    TraceOutcome(..)
  , runTracingRedexDet
  , runTracingRedexDetWith
    -- * The Monad (advanced use)
  , TracingRedexDet
  ) where

import TypedRedex.Logic
import TypedRedex.DSL.Fresh (LTerm)
import TypedRedex.Interp.Format (formatConWith, intercalate, TermFormatter(..), DefaultTermFormatter(..))
import TypedRedex.Interp.Tracing (Derivation(..))
import Control.Monad.State
import Control.Monad (guard, forM_)
import Unsafe.Coerce (unsafeCoerce)

--------------------------------------------------------------------------------
-- Public result type
--------------------------------------------------------------------------------

data TraceOutcome a
  = TraceSuccess a Derivation
  | TraceFailure Derivation
  deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Internal failure tracking
--------------------------------------------------------------------------------

data FailureInfo = FailureInfo
  { fiDepth :: !Int
  , fiDeriv :: Maybe Derivation
  , fiGoal  :: Maybe String
  }

emptyFailure :: FailureInfo
emptyFailure = FailureInfo { fiDepth = 0, fiDeriv = Nothing, fiGoal = Nothing }

goalFailure :: String -> FailureInfo
goalFailure goalStr = FailureInfo { fiDepth = 1, fiDeriv = Nothing, fiGoal = Just goalStr }

derivFailure :: Derivation -> FailureInfo
derivFailure d = FailureInfo { fiDepth = derivDepth d, fiDeriv = Just d, fiGoal = Nothing }

betterFailure :: FailureInfo -> FailureInfo -> FailureInfo
betterFailure a b
  | fiDepth a > fiDepth b = a
  | fiDepth b > fiDepth a = b
  | otherwise =
      -- Tie-break deterministically:
      -- prefer a derivation over only a goal string, and prefer left bias.
      case (fiDeriv a, fiDeriv b, fiGoal a, fiGoal b) of
        (Just _, Nothing, _, _) -> a
        (Nothing, Just _, _, _) -> b
        (Nothing, Nothing, Just _, Nothing) -> a
        (Nothing, Nothing, Nothing, Just _) -> b
        _ -> a

derivDepth :: Derivation -> Int
derivDepth (Leaf _) = 1
derivDepth (Deriv "__goal__" _ cs) = maximum (0 : map derivDepth cs)
derivDepth (Deriv _ _ cs) = 1 + maximum (0 : map derivDepth cs)

--------------------------------------------------------------------------------
-- Derivation tracking state (copy of TracingRedex, but failure-aware)
--------------------------------------------------------------------------------

type V s t = RVar (TracingRedexDet s) t

-- | An existentially wrapped hash constraint: name # term
data HashConstraint s = forall name term.
  (NominalAtom name, LogicType name, LogicType term, Hash name term) =>
  HashConstraint (LTerm name (TracingRedexDet s)) (LTerm term (TracingRedexDet s))

data DerivFrame s = DerivFrame
  { frameRule     :: String
  , frameTerms    :: [CapturedTerm (TracingRedexDet s)]
  , frameChildren :: [Derivation]
  , frameFormat   :: [String] -> String
  }

data TracingState s = TracingState
  { tsSubst      :: forall t. V s t -> Maybe t
  , tsNextVar    :: VarRepr
  , tsDerivStack :: [DerivFrame s]
  , tsFormatter  :: String -> [String] -> String
  , tsFreshCounter :: !Int
  , tsHashConstraints :: [HashConstraint s]
  }

-- | Default format for top-level frame (just joins args with ", ")
defaultTopFormat :: [String] -> String
defaultTopFormat = intercalate ", "

emptyStateWith :: (String -> [String] -> String) -> TracingState s
emptyStateWith fmt = TracingState
  { tsSubst = \v -> error $ "Invalid variable " ++ show (varToInt v)
  , tsNextVar = 0
  , tsDerivStack = [DerivFrame "__goal__" [] [] defaultTopFormat]
  , tsFormatter = fmt
  , tsFreshCounter = 0
  , tsHashConstraints = []
  }

varToInt :: V s t -> Int
varToInt (TVar n) = n

readSubst :: V s a -> TracingState s -> Maybe a
readSubst v s = tsSubst s v

updateSubst :: V s a -> Maybe a -> TracingState s -> TracingState s
updateSubst v a s = s { tsSubst = \v' -> if varEq' v v' then unsafeCoerce a else tsSubst s v' }
  where
    varEq' (TVar a') (TVar b) = a' == b

succVar :: TracingState s -> TracingState s
succVar s = s { tsNextVar = succ (tsNextVar s) }

pushFrame :: String -> [CapturedTerm (TracingRedexDet s)] -> ([String] -> String) -> TracingState s -> TracingState s
pushFrame rule terms format s =
  s { tsDerivStack = DerivFrame rule terms [] format : tsDerivStack s }

--------------------------------------------------------------------------------
-- Deterministic "search" monad: carries failures instead of dropping state
--------------------------------------------------------------------------------

data Outcome s a
  = Ok a (TracingState s)
  | Fail FailureInfo (TracingState s)

newtype TracingRedexDet s a = TracingRedexDet { runDet :: TracingState s -> Outcome s a }

instance Functor (TracingRedexDet s) where
  fmap f (TracingRedexDet m) = TracingRedexDet $ \s ->
    case m s of
      Ok a s'      -> Ok (f a) s'
      Fail fi s'   -> Fail fi s'

instance Applicative (TracingRedexDet s) where
  pure a = TracingRedexDet $ \s -> Ok a s
  TracingRedexDet mf <*> TracingRedexDet ma = TracingRedexDet $ \s ->
    case mf s of
      Ok f s' ->
        case ma s' of
          Ok a s''    -> Ok (f a) s''
          Fail fi s'' -> Fail fi s''
      Fail fi s' -> Fail fi s'

instance Monad (TracingRedexDet s) where
  TracingRedexDet ma >>= f = TracingRedexDet $ \s ->
    case ma s of
      Ok a s' ->
        let TracingRedexDet mb = f a
        in mb s'
      Fail fi s' -> Fail fi s'

instance Alternative (TracingRedexDet s) where
  empty = TracingRedexDet $ \s -> Fail emptyFailure s
  TracingRedexDet a <|> TracingRedexDet b = TracingRedexDet $ \s0 ->
    case a s0 of
      Ok x s1       -> Ok x s1
      Fail fa _sA   ->
        case b s0 of
          Ok y s2     -> Ok y s2
          Fail fb _sB -> Fail (betterFailure fa fb) s0

instance MonadState (TracingState s) (TracingRedexDet s) where
  state f = TracingRedexDet $ \s ->
    let (a, s') = f s
    in Ok a s'

--------------------------------------------------------------------------------
-- Redex instance
--------------------------------------------------------------------------------

instance Redex (TracingRedexDet s) where
  newtype RVar (TracingRedexDet s) t = TVar VarRepr
    deriving (Functor, Show)

  fresh_ FreshVar k = do
    v <- TVar <$> gets tsNextVar
    modify $ succVar . updateSubst v Nothing
    k (Var v)

  fresh_ (ArgVar x) k = do
    v <- TVar <$> gets tsNextVar
    modify $ succVar . updateSubst v (Just x)
    k (Var v)

  unify = flatteningUnify unif
    where
      unif v (Free v') | unVar v `varEq` unVar v' = pure ()
      unif v y
        | occursCheck v y = empty
        | otherwise = do
            x <- gets (readSubst (unVar v))
            case x of
              Nothing -> do
                modify $ updateSubst (unVar v) (Just y)
                recheckHashConstraints
              Just x' -> unify y x'

  displayVar (TVar v) = displayVarInt v

  suspend = id

  -- Failure-aware call_:
  -- on success, build a derivation node and attach to parent;
  -- on failure, attach either an "error (no rule applies)" leaf (for top wrappers)
  -- or a partial derivation (for matched rules that made progress).
  call_ _ rel = TracingRedexDet $ \s0 ->
    let s1 = pushFrame (relRule rel) (relTerms rel) (relFormat rel) s0
        TracingRedexDet body = relBody rel
    in case body s1 of
      Ok () s2 ->
        let TracingRedexDet pop = popFrameSuccess
        in pop s2
      Fail fi s2 ->
        let TracingRedexDet pop = popFrameFailure fi
        in pop s2

--------------------------------------------------------------------------------
-- Pop frame helpers
--------------------------------------------------------------------------------

popFrameSuccess :: TracingRedexDet s ()
popFrameSuccess = TracingRedexDet $ \st ->
  case tsDerivStack st of
    (current:parent:rest) ->
      let (args, st1) = runResolveAll st (frameTerms current)
          conclusion = frameFormat current args
          deriv = Deriv (frameRule current) conclusion (reverse $ frameChildren current)
          parent' = parent { frameChildren = deriv : frameChildren parent }
      in Ok () st1 { tsDerivStack = parent' : rest }
    _ -> Ok () st

popFrameFailure :: FailureInfo -> TracingRedexDet s ()
popFrameFailure fi0 = TracingRedexDet $ \st ->
  case tsDerivStack st of
    (current:parent:rest) ->
      let -- If the failing body already computed a best derivation, treat it as an
          -- additional child of the current frame.
          --
          -- Important: only attach it when the current frame has *no* children.
          -- If the current frame already accumulated premise derivations, the
          -- best failing subtree is (typically) already represented among those
          -- children via normal call-frame attachment. Attaching it again here
          -- can duplicate the same stuck-leaf in the rendered tree.
          currentWithChild =
            case fiDeriv fi0 of
              Nothing -> current
              Just d
                | null (frameChildren current) -> current { frameChildren = d : frameChildren current }
                | otherwise -> current
          -- If nothing matched and this is a "__goal__" wrapper, manufacture the
          -- explicit error leaf at this goal.
          (currentFinal, fi1, st1) =
            if null (frameChildren currentWithChild) && frameRule currentWithChild == "__goal__"
              then
                let (args, stR) = runResolveAllHoles st (frameTerms currentWithChild)
                    goalStr = frameFormat currentWithChild args
                    err = Deriv "error (no rule applies)" goalStr []
                    cur' = currentWithChild { frameChildren = err : frameChildren currentWithChild }
                in (cur', derivFailure err, stR)
              else (currentWithChild, fi0, st)
          -- If we still have no children, treat this call as a mismatch: do not
          -- attach a node (it didn't make progress), but propagate a goal string
          -- upward so wrappers can produce a stuck-goal error.
      in if null (frameChildren currentFinal)
           then
             let (args, stR) = runResolveAllHoles st1 (frameTerms currentFinal)
                 goalStr = frameFormat currentFinal args
                 parentState = stR { tsDerivStack = parent : rest }
             in Fail (betterFailure fi1 (goalFailure goalStr)) parentState
           else
             let (args, stR) = runResolveAllHoles st1 (frameTerms currentFinal)
                 conclusion = frameFormat currentFinal args
                 derivNode = Deriv (frameRule currentFinal) conclusion (reverse $ frameChildren currentFinal)
                 parent' = parent { frameChildren = derivNode : frameChildren parent }
                 stOut = stR { tsDerivStack = parent' : rest }
             in Fail (betterFailure fi1 (derivFailure derivNode)) stOut
    _ ->
      -- If we're missing a parent frame (should only happen at top),
      -- fall back to a leaf built from whatever info we have.
      let fallback =
            case fiDeriv fi0 of
              Just d  -> d
              Nothing ->
                case fiGoal fi0 of
                  Just g  -> Deriv "error (no rule applies)" g []
                  Nothing -> Leaf "error"
      in Fail (derivFailure fallback) st

runResolveAll :: TracingState s -> [CapturedTerm (TracingRedexDet s)] -> ([String], TracingState s)
runResolveAll st0 terms =
  case runDet (mapM resolveCaptured terms) st0 of
    Ok args st'    -> (args, st')
    Fail _fi st'   -> ([], st')  -- resolution itself should not fail; defensive

-- | Like 'runResolveAll', but prints unbound variables as '_' for diagnostics.
--
-- This keeps stuck-goal leaves readable by avoiding noisy internal variable
-- names such as @x37@ in output positions.
runResolveAllHoles :: TracingState s -> [CapturedTerm (TracingRedexDet s)] -> ([String], TracingState s)
runResolveAllHoles st0 terms =
  case runDet (mapM resolveCapturedHole terms) st0 of
    Ok args st'    -> (args, st')
    Fail _fi st'   -> ([], st')

resolveCaptured :: CapturedTerm (TracingRedexDet s) -> TracingRedexDet s String
resolveCaptured (CapturedTerm term) = prettyResolved term

resolveCapturedHole :: CapturedTerm (TracingRedexDet s) -> TracingRedexDet s String
resolveCapturedHole (CapturedTerm term) = prettyResolvedHole term

prettyResolved :: forall a s. LogicType a => LTerm a (TracingRedexDet s) -> TracingRedexDet s String
prettyResolved (Free v) = do
  mx <- gets (readSubst (unVar v))
  case mx of
    Nothing -> pure $ displayVar (unVar v)
    Just x  -> prettyResolved x
prettyResolved (Ground r) = do
  let (name, fields) = quote r
  fieldStrs <- mapM prettyField fields
  case formatCon @a name fieldStrs of
    Just s  -> pure s
    Nothing -> do
      fmt <- gets tsFormatter
      pure $ fmt name fieldStrs
  where
    prettyField :: forall parent. Field parent (RVar (TracingRedexDet s)) -> TracingRedexDet s String
    prettyField (Field _ logic) = prettyResolvedAny logic

    prettyResolvedAny :: forall t. LogicType t => Logic t (RVar (TracingRedexDet s)) -> TracingRedexDet s String
    prettyResolvedAny (Free v) = do
      mx <- gets (readSubst (unVar v))
      case mx of
        Nothing -> pure $ displayVar (unVar v)
        Just x  -> prettyResolvedAny x
    prettyResolvedAny (Ground r') = do
      let (name', fields') = quote r'
      fieldStrs' <- mapM prettyField fields'
      case formatCon @t name' fieldStrs' of
        Just s  -> pure s
        Nothing -> do
          fmt <- gets tsFormatter
          pure $ fmt name' fieldStrs'

prettyResolvedHole :: forall a s. LogicType a => LTerm a (TracingRedexDet s) -> TracingRedexDet s String
prettyResolvedHole (Free v) = do
  mx <- gets (readSubst (unVar v))
  case mx of
    Nothing -> pure "_"
    Just x  -> prettyResolvedHole x
prettyResolvedHole (Ground r) = do
  let (name, fields) = quote r
  fieldStrs <- mapM prettyField fields
  case formatCon @a name fieldStrs of
    Just s  -> pure s
    Nothing -> do
      fmt <- gets tsFormatter
      pure $ fmt name fieldStrs
  where
    prettyField :: forall parent. Field parent (RVar (TracingRedexDet s)) -> TracingRedexDet s String
    prettyField (Field _ logic) = prettyResolvedAny logic

    prettyResolvedAny :: forall t. LogicType t => Logic t (RVar (TracingRedexDet s)) -> TracingRedexDet s String
    prettyResolvedAny (Free v) = do
      mx <- gets (readSubst (unVar v))
      case mx of
        Nothing -> pure "_"
        Just x  -> prettyResolvedAny x
    prettyResolvedAny (Ground r') = do
      let (name', fields') = quote r'
      fieldStrs' <- mapM prettyField fields'
      case formatCon @t name' fieldStrs' of
        Just s  -> pure s
        Nothing -> do
          fmt <- gets tsFormatter
          pure $ fmt name' fieldStrs'

--------------------------------------------------------------------------------
-- Evaluation, fresh names, hash, negation
--------------------------------------------------------------------------------

instance EqVar (TracingRedexDet s) where
  varEq (TVar a) (TVar b) = a == b

instance RedexEval (TracingRedexDet s) where
  derefVar v = do
    x <- gets (readSubst (unVar v))
    case x of
      Nothing -> error $ "Unbound variable: " ++ displayVar (unVar v)
      Just val -> evalLogic val
    where
      evalLogic :: LogicType a => LTerm a (TracingRedexDet s) -> TracingRedexDet s a
      evalLogic (Free v') = derefVar v'
      evalLogic (Ground r) = derefVal evalLogic r

instance RedexFresh (TracingRedexDet s) where
  freshInt = do
    s <- get
    let n = tsFreshCounter s
    put s { tsFreshCounter = n + 1 }
    pure n

-- Hash constraint handling (same as Stream-based tracer)

walkL :: LogicType a => LTerm a (TracingRedexDet s) -> TracingRedexDet s (LTerm a (TracingRedexDet s))
walkL (Ground r) = pure (Ground r)
walkL (Free v) = do
  mx <- gets (readSubst (unVar v))
  case mx of
    Nothing -> pure (Free v)
    Just lt -> walkL lt

isGroundL :: LogicType a => LTerm a (TracingRedexDet s) -> TracingRedexDet s (Maybe a)
isGroundL lt = do
  lt' <- walkL lt
  case lt' of
    Ground r -> pure (reify r)
    Free _   -> pure Nothing

addHashConstraint :: (NominalAtom name, LogicType name, LogicType term, Hash name term)
                  => LTerm name (TracingRedexDet s) -> LTerm term (TracingRedexDet s) -> TracingRedexDet s ()
addHashConstraint nameL termL = modify $ \s ->
  s { tsHashConstraints = HashConstraint nameL termL : tsHashConstraints s }

checkHashConstraint :: HashConstraint s -> TracingRedexDet s ()
checkHashConstraint (HashConstraint nameL termL) = do
  mName <- isGroundL nameL
  mTerm <- isGroundL termL
  case (mName, mTerm) of
    (Just name, Just term) -> guard (not $ occursIn name term)
    _ -> addHashConstraint nameL termL

recheckHashConstraints :: TracingRedexDet s ()
recheckHashConstraints = do
  constraints <- gets tsHashConstraints
  modify $ \s -> s { tsHashConstraints = [] }
  forM_ constraints checkHashConstraint

instance RedexHash (TracingRedexDet s) where
  hash nameL termL = do
    nameL' <- walkL nameL
    termL' <- walkL termL
    mName <- isGroundL nameL'
    mTerm <- isGroundL termL'
    case (mName, mTerm) of
      (Just name, Just term) -> guard (not $ occursIn name term)
      _ -> addHashConstraint nameL' termL'

instance RedexNeg (TracingRedexDet s) where
  neg goal = TracingRedexDet $ \s0 ->
    let TracingRedexDet g = goal
    in case g s0 of
      Ok _ _    -> Fail emptyFailure s0
      Fail _ _  -> Ok () s0

--------------------------------------------------------------------------------
-- Running
--------------------------------------------------------------------------------

runTracingRedexDet :: (forall s. TracingRedexDet s a) -> TraceOutcome a
runTracingRedexDet = runTracingRedexDetWith DefaultTermFormatter

runTracingRedexDetWith :: TermFormatter fmt => fmt -> (forall s. TracingRedexDet s a) -> TraceOutcome a
runTracingRedexDetWith fmt (TracingRedexDet r) =
  case r (emptyStateWith (formatConWith fmt)) of
    Ok a st ->
      let d = extractDeriv st
      in TraceSuccess a d
    Fail fi st ->
      let d =
            case fiDeriv fi of
              Just d' -> d'
              Nothing -> extractDeriv st
      in TraceFailure d

extractDeriv :: TracingState s -> Derivation
extractDeriv st =
  case tsDerivStack st of
    [frame] ->
      case frameChildren frame of
        [d] -> d
        ds  -> Deriv "__goal__" "" (reverse ds)
    (frame:_) -> Deriv (frameRule frame) "" (reverse $ frameChildren frame)
    [] -> Leaf "?"
