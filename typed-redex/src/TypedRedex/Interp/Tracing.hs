{-# LANGUAGE TypeFamilies, DeriveFunctor, Rank2Types, GeneralisedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs, ExistentialQuantification, ScopedTypeVariables #-}

-- | TracingRedex: A derivation-tracking interpreter for TypedRedex
--
-- = Overview
--
-- This interpreter extends SubstRedex with derivation tree construction.
-- It tracks which rules are applied and builds proof trees.
--
-- = Architecture
--
-- @
-- TracingRedex s a = StateT (TracingState s) Stream a
--                     ├─ TracingState: substitution + derivation stack
--                     └─ Stream: lazy list with interleaving
--
-- TracingState contains:
--   ├─ tsSubst: variable substitution (shared with SubstRedex via SubstCore)
--   ├─ tsNextVar: fresh variable counter
--   └─ tsDerivStack: stack of derivation frames
-- @
--
-- = How Derivations Are Built
--
-- The derivation stack tracks nested rule applications:
--
-- @
-- 1. call_ pushes frame with CapturedTerms (not strings!)
-- 2. (premise calls add children to current frame)
-- 3. popFrame resolves terms using current substitution, builds Derivation
-- @
--
-- = Key Improvement: Deferred Resolution
--
-- Unlike earlier versions that captured pre-computed strings, this version
-- stores CapturedTerms (existentially wrapped logic terms). Resolution to
-- strings happens at popFrame time, AFTER unification completes.
-- This ensures derivations show actual values, not unresolved variables.

module TypedRedex.Interp.Tracing
  ( -- * Running with Derivations
    runTracingRedex
  , runTracingRedexWith
  , runWithDerivation
  , runWithDerivationWith
    -- * Derivation Trees
  , Derivation(..)
  , prettyDerivation
  , prettyDerivationWith
  , substInDerivation
    -- * Judgment Formatting (re-exported from Format)
  , JudgmentFormatter(..)
  , defaultFormatJudgment
    -- * Legacy alias
  , defaultFormatConclusion
    -- * The Monad (for advanced use)
  , TracingRedex
  ) where

import TypedRedex.Core.Internal.Redex
import TypedRedex.Core.Internal.Logic
import TypedRedex.Core.Internal.Unify (flatteningUnify, occursCheck)
import TypedRedex.Core.Internal.SubstCore (VarRepr, displayVarInt)
import TypedRedex.DSL.Fresh (LTerm, LVar)
import TypedRedex.Interp.Format (formatCon, formatConWith, intercalate, TermFormatter(..), DefaultTermFormatter(..), JudgmentFormatter(..), defaultFormatJudgment)
import TypedRedex.Interp.Stream
import TypedRedex.Interp.Subst (RedexFresh(..))
import TypedRedex.Nominal.Nom (NominalAtom)
import TypedRedex.Nominal.Hash (Hash(..), RedexHash(..))
import Control.Monad.State
import Control.Monad (guard, forM_)
import Control.Applicative
import Unsafe.Coerce (unsafeCoerce)

-- | Legacy alias for backward compatibility
defaultFormatConclusion :: String -> [String] -> String
defaultFormatConclusion = defaultFormatJudgment

--------------------------------------------------------------------------------
-- Derivation Trees
--------------------------------------------------------------------------------

-- | A derivation tree representing a proof.
--
-- @
-- Deriv "β" ["(λ.e) v", "e'"] [premise1, premise2]
--   represents:
--
--   premise1    premise2
--   ─────────────────────── [β]
--        (λ.e) v → e'
-- @
data Derivation
  = Deriv
      { derivRule :: String           -- ^ Rule name
      , derivArgs :: [String]         -- ^ Arguments (pretty-printed after resolution)
      , derivChildren :: [Derivation] -- ^ Premises (sub-derivations)
      }
  | Leaf String [String]              -- ^ Axiom with arguments
  deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Pretty-printing Derivations
--------------------------------------------------------------------------------

-- | Pretty-print a derivation tree using the default formatter.
prettyDerivation :: Derivation -> String
prettyDerivation = prettyDerivationWith DefaultTermFormatter

-- | Pretty-print a derivation tree with a custom formatter.
--
-- Renders premises horizontally above the inference line:
--
-- @
-- Γ ⊢ e1 ⇒ A → B   Γ ⊢ e2 ⇐ A
-- ──────────────────────────── [⇒App]
--        Γ ⊢ e1 e2 ⇒ B
-- @
prettyDerivationWith :: JudgmentFormatter fmt => fmt -> Derivation -> String
prettyDerivationWith fmt d = unlines $ renderDeriv d
  where
    renderDeriv :: Derivation -> [String]
    renderDeriv (Leaf name _) = [name]
    renderDeriv (Deriv "top" _ children) =
      case children of
        [c] -> renderDeriv c
        cs -> concatMap renderDeriv cs
    renderDeriv (Deriv name args children) =
      let conclusion = formatJudgment fmt name args
          childBlocks = map renderDeriv children
      in if null childBlocks
         then -- Axiom: just the line and conclusion
           let lineWidth = length conclusion + 4
               line = replicate lineWidth '─' ++ " [" ++ name ++ "]"
           in [line, conclusion]
         else
           let -- Combine child blocks horizontally
               combined = foldr1 sideBySide childBlocks
               premiseWidth = if null combined then 0 else maximum (map length combined)
               concWidth = length conclusion
               lineWidth = max premiseWidth concWidth
               line = replicate lineWidth '─' ++ " [" ++ name ++ "]"
               concPad = (lineWidth - concWidth) `div` 2
               paddedConc = replicate concPad ' ' ++ conclusion
           in combined ++ [line, paddedConc]

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

-- | Substitute a variable name in a derivation with an actual value.
substInDerivation :: String -> String -> Derivation -> Derivation
substInDerivation var val (Leaf name args) = Leaf name (map subst args)
  where subst s = if s == var then val else s
substInDerivation var val (Deriv name args children) =
  Deriv name (map subst args) (map (substInDerivation var val) children)
  where subst s = if s == var then val else s

--------------------------------------------------------------------------------
-- Tracing State
--------------------------------------------------------------------------------

type V s t = RVar (TracingRedex s) t

-- | An existentially wrapped hash constraint: name # term
data HashConstraint s = forall name term.
  (NominalAtom name, LogicType name, LogicType term, Hash name term) =>
  HashConstraint (LTerm name (TracingRedex s)) (LTerm term (TracingRedex s))

-- | A frame in the derivation stack.
--
-- When we enter a rule, we push a frame with CapturedTerms. As premises
-- are proved, their derivations are added to frameChildren. When the rule
-- completes, we resolve the captured terms to strings and build a Derivation.
data DerivFrame s = DerivFrame
  { frameName     :: String                           -- ^ Rule name
  , frameTerms    :: [CapturedTerm (TracingRedex s)]  -- ^ Captured terms (resolved at pop time)
  , frameChildren :: [Derivation]                     -- ^ Accumulated premise derivations
  }

-- | Complete state for the tracing interpreter.
data TracingState s = TracingState
  { tsSubst      :: forall t. V s t -> Maybe t  -- ^ Substitution
  , tsNextVar    :: VarRepr                      -- ^ Fresh var counter
  , tsDerivStack :: [DerivFrame s]               -- ^ Derivation stack
  , tsFormatter  :: String -> [String] -> String -- ^ Term formatter function
  , tsFreshCounter :: !Int                       -- ^ Counter for fresh nominal atoms
  , tsHashConstraints :: [HashConstraint s]      -- ^ Lazy hash constraints: name # term
  }

emptyState :: TracingState s
emptyState = emptyStateWith formatCon

emptyStateWith :: (String -> [String] -> String) -> TracingState s
emptyStateWith fmt = TracingState
  { tsSubst = \v -> error $ "Invalid variable " ++ show (varToInt v)
  , tsNextVar = 0
  , tsDerivStack = [DerivFrame "top" [] []]  -- Start with top-level frame
  , tsFormatter = fmt
  , tsFreshCounter = 0
  , tsHashConstraints = []
  }

varToInt :: V s t -> Int
varToInt (TVar n) = n

-- | Read a variable's binding.
readSubst :: V s a -> TracingState s -> Maybe a
readSubst v s = tsSubst s v

-- | Update a variable's binding.
updateSubst :: V s a -> Maybe a -> TracingState s -> TracingState s
updateSubst v a s = s { tsSubst = \v' -> if varEq' v v' then unsafeCoerce a else tsSubst s v' }
  where
    varEq' (TVar a') (TVar b) = a' == b

-- | Increment the variable counter.
succVar :: TracingState s -> TracingState s
succVar s = s { tsNextVar = succ (tsNextVar s) }

-- | Push a new derivation frame onto the stack with captured terms.
pushFrame :: String -> [CapturedTerm (TracingRedex s)] -> TracingState s -> TracingState s
pushFrame name terms s = s { tsDerivStack = DerivFrame name terms [] : tsDerivStack s }

--------------------------------------------------------------------------------
-- Tracing Redex Monad
--------------------------------------------------------------------------------

-- | The TracingRedex monad.
--
-- Like SubstRedex but with derivation tracking state.
newtype TracingRedex s a = TracingRedex (StateT (TracingState s) Stream a)
  deriving (Functor, Applicative, Monad)

instance Alternative (TracingRedex s) where
  empty = TracingRedex $ StateT $ \_ -> Empty
  TracingRedex a <|> TracingRedex b = TracingRedex $ StateT $ \s ->
    runStateT a s <|> runStateT b s

instance MonadState (TracingState s) (TracingRedex s) where
  state = TracingRedex . state

--------------------------------------------------------------------------------
-- Redex Instance
--------------------------------------------------------------------------------

instance Redex (TracingRedex s) where
  newtype RVar (TracingRedex s) t = TVar VarRepr
    deriving (Functor, Show)

  -- | Allocate fresh variables
  fresh_ FreshVar k = do
    v <- TVar <$> gets tsNextVar
    modify $ succVar . updateSubst v Nothing
    k (Var v)

  fresh_ (ArgVar x) k = do
    v <- TVar <$> gets tsNextVar
    modify $ succVar . updateSubst v (Just x)
    k (Var v)

  -- | Unification
  unify = flatteningUnify unif
    where
      unif v y
        | occursCheck v y = empty
        | otherwise = do
            x <- gets (readSubst (unVar v))
            case x of
              Nothing -> do
                modify $ updateSubst (unVar v) (Just y)
                recheckHashConstraints  -- Check hash constraints after binding
              Just x' -> unify y x'

  -- | Display variable
  displayVar (TVar v) = displayVarInt v

  -- | Suspend for fair interleaving
  suspend (TracingRedex r) = TracingRedex $ mapStateT Immature r

  -- | Custom call_ that handles derivation frame management.
  --
  -- 1. Push frame with captured terms
  -- 2. Execute body
  -- 3. Pop frame, resolve terms, build derivation
  call_ Opaque rel = do
    modify $ pushFrame (relName rel) (relTerms rel)
    suspend (relBody rel)
    popFrameAndResolve

  call_ Transparent rel = do
    modify $ pushFrame (relName rel) (relTerms rel)
    relBody rel
    popFrameAndResolve

-- | Pop frame, resolve captured terms to strings, build derivation.
-- This is where deferred resolution happens - terms are resolved NOW,
-- after unification has completed.
popFrameAndResolve :: TracingRedex s ()
popFrameAndResolve = do
  st <- get
  case tsDerivStack st of
    (current:parent:rest) -> do
      -- Resolve captured terms to strings using current substitution
      args <- mapM resolveCaptured (frameTerms current)
      let deriv = Deriv (frameName current) args (reverse $ frameChildren current)
          parent' = parent { frameChildren = deriv : frameChildren parent }
      put $ st { tsDerivStack = parent' : rest }
    _ -> pure ()  -- At top level, don't pop

-- | Resolve a captured term to a string using current substitution.
resolveCaptured :: CapturedTerm (TracingRedex s) -> TracingRedex s String
resolveCaptured (CapturedTerm term) = prettyResolved term

-- | Pretty-print a logic term after resolving through substitution.
prettyResolved :: LogicType a => LTerm a (TracingRedex s) -> TracingRedex s String
prettyResolved (Free v) = do
  mx <- gets (readSubst (unVar v))
  case mx of
    Nothing -> pure $ displayVar (unVar v)  -- Still unbound, show variable name
    Just x  -> prettyResolved x     -- Bound, resolve and recurse
prettyResolved (Ground r) = do
  fmt <- gets tsFormatter
  let (con, fields) = quote r
  fieldStrs <- mapM prettyField fields
  pure $ fmt (constructorName con) fieldStrs
  where
    prettyField :: Field a (RVar (TracingRedex s)) -> TracingRedex s String
    prettyField (Field _ logic) = prettyResolvedAny logic

    prettyResolvedAny :: LogicType t => Logic t (RVar (TracingRedex s)) -> TracingRedex s String
    prettyResolvedAny (Free v) = do
      mx <- gets (readSubst (unVar v))
      case mx of
        Nothing -> pure $ displayVar (unVar v)
        Just x  -> prettyResolvedAny x
    prettyResolvedAny (Ground r') = do
      fmt <- gets tsFormatter
      let (con', fields') = quote r'
      fieldStrs' <- mapM prettyField fields'
      pure $ fmt (constructorName con') fieldStrs'

--------------------------------------------------------------------------------
-- RedexStructure Instance (Derivation Tracking)
--------------------------------------------------------------------------------

instance RedexStructure (TracingRedex s) where
  -- | Push a new derivation frame when entering a rule
  -- Note: with CapturedTerm, we need the terms, but onRuleEnter only gets strings
  -- This is mainly for backward compatibility - the real work is done in call_
  onRuleEnter name args = modify $ \s ->
    s { tsDerivStack = DerivFrame name [] [] : tsDerivStack s }

  -- | Pop frame when exiting a rule
  onRuleExit _ = popFrameAndResolve

  -- | Wrap premise call (default: just run body)
  withPremise _ _ = id

instance EqVar (TracingRedex s) where
  varEq (TVar a) (TVar b) = a == b

instance RedexEval (TracingRedex s) where
  derefVar v = do
    x <- gets (readSubst (unVar v))
    case x of
      Nothing -> error $ "Unbound variable: " ++ displayVar (unVar v)
      Just val -> evalLogic val
    where
      evalLogic :: LogicType a => LTerm a (TracingRedex s) -> TracingRedex s a
      evalLogic (Free v') = derefVar v'
      evalLogic (Ground r) = derefVal evalLogic r

instance RedexFresh (TracingRedex s) where
  freshInt = do
    s <- get
    let n = tsFreshCounter s
    put s { tsFreshCounter = n + 1 }
    pure n

--------------------------------------------------------------------------------
-- Hash Constraints
--------------------------------------------------------------------------------

-- | Walk a logic term to its root (following variable bindings).
walkL :: LogicType a => LTerm a (TracingRedex s) -> TracingRedex s (LTerm a (TracingRedex s))
walkL (Ground r) = pure (Ground r)
walkL (Free v) = do
  mx <- gets (readSubst (unVar v))
  case mx of
    Nothing -> pure (Free v)  -- Unbound variable
    Just lt -> walkL lt       -- Follow the binding

-- | Check if a logic term is ground (no unbound variables at the root).
isGroundL :: LogicType a => LTerm a (TracingRedex s) -> TracingRedex s (Maybe a)
isGroundL lt = do
  lt' <- walkL lt
  case lt' of
    Ground r -> pure (reify r)
    Free _   -> pure Nothing

-- | Add a hash constraint to the constraint store.
addHashConstraint :: (NominalAtom name, LogicType name, LogicType term, Hash name term)
                  => LTerm name (TracingRedex s) -> LTerm term (TracingRedex s) -> TracingRedex s ()
addHashConstraint nameL termL = modify $ \s ->
  s { tsHashConstraints = HashConstraint nameL termL : tsHashConstraints s }

-- | Check a single hash constraint.
checkHashConstraint :: HashConstraint s -> TracingRedex s ()
checkHashConstraint (HashConstraint nameL termL) = do
  mName <- isGroundL nameL
  mTerm <- isGroundL termL
  case (mName, mTerm) of
    (Just name, Just term) ->
      -- Both ground: check immediately
      guard (not $ occursIn name term)
    _ ->
      -- At least one is still a variable: keep the constraint
      addHashConstraint nameL termL

-- | Re-check all hash constraints (called after unification).
recheckHashConstraints :: TracingRedex s ()
recheckHashConstraints = do
  constraints <- gets tsHashConstraints
  -- Clear the constraint store before re-checking
  modify $ \s -> s { tsHashConstraints = [] }
  -- Re-check each constraint (will re-add if still not ground)
  forM_ constraints checkHashConstraint

instance RedexHash (TracingRedex s) where
  hash nameL termL = do
    -- Walk to roots
    nameL' <- walkL nameL
    termL' <- walkL termL
    -- Try to get ground values
    mName <- isGroundL nameL'
    mTerm <- isGroundL termL'
    case (mName, mTerm) of
      (Just name, Just term) ->
        -- Both ground: check immediately, fail if violated
        guard (not $ occursIn name term)
      _ ->
        -- At least one is a variable: store constraint for later
        addHashConstraint nameL' termL'

instance RedexNeg (TracingRedex s) where
  -- | Negation-as-failure: succeed if goal has no solutions
  neg goal = do
    s0 <- get
    let TracingRedex goalComp = goal
        answerStream = execStateT goalComp s0
    case firstAnswer answerStream of
      Nothing -> pure ()
      Just _  -> empty
    where
      firstAnswer :: Stream a -> Maybe a
      firstAnswer Empty = Nothing
      firstAnswer (Mature a _) = Just a
      firstAnswer (Immature rest) = firstAnswer rest

--------------------------------------------------------------------------------
-- Running
--------------------------------------------------------------------------------

-- | Run a tracing computation and return results with derivations.
--
-- @
-- runTracingRedex $ fresh $ \\ty -> do
--   embed $ synth emptyCtx expr ty
--   eval ty
-- -- Returns: Stream [(inferredType, derivationTree)]
-- @
runTracingRedex :: (forall s. TracingRedex s a) -> Stream (a, Derivation)
runTracingRedex = runTracingRedexWith DefaultTermFormatter

-- | Run a tracing computation with a custom term formatter.
runTracingRedexWith :: TermFormatter fmt => fmt -> (forall s. TracingRedex s a) -> Stream (a, Derivation)
runTracingRedexWith fmt (TracingRedex r) = fmap extractDeriv $ runStateT r (emptyStateWith (formatConWith fmt))
  where
    extractDeriv (result, st) =
      let deriv = case tsDerivStack st of
            [frame] -> case frameChildren frame of
              [d] -> d
              ds -> Deriv "top" [] (reverse ds)
            (frame:_) -> Deriv (frameName frame) [] (reverse $ frameChildren frame)
            [] -> Leaf "?" []
      in (result, deriv)

-- | Alias for 'runTracingRedex'.
runWithDerivation :: (forall s. TracingRedex s a) -> Stream (a, Derivation)
runWithDerivation = runTracingRedex

-- | Alias for 'runTracingRedexWith'.
runWithDerivationWith :: TermFormatter fmt => fmt -> (forall s. TracingRedex s a) -> Stream (a, Derivation)
runWithDerivationWith = runTracingRedexWith
