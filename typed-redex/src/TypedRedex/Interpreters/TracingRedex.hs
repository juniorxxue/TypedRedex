{-# LANGUAGE TypeFamilies, DeriveFunctor, Rank2Types, GeneralisedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances #-}

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
--   ├─ tsSubst: variable substitution (like SubstRedex)
--   ├─ tsNextVar: fresh variable counter
--   └─ tsDerivStack: stack of derivation frames
-- @
--
-- = How Derivations Are Built
--
-- The derivation stack tracks nested rule applications:
--
-- @
-- 1. onRuleEnter "β" args  → push DerivFrame "β" args []
-- 2. (premise calls add children to current frame)
-- 3. onRuleExit "β"        → pop frame, create Derivation, add to parent
-- @
--
-- = Implementing Redex Hooks
--
-- This interpreter uses all the structure tracking hooks:
--
-- * 'onRuleEnter': Push a new derivation frame
-- * 'onRuleExit': Pop frame, build derivation node, attach to parent
-- * 'suspend': Wrap in Immature for fair search (like SubstRedex)

module TypedRedex.Interpreters.TracingRedex
  ( -- * Running with Derivations
    runTracingRedex
  , runWithDerivation
    -- * Derivation Trees
  , Derivation(..)
  , prettyDerivation
  , substInDerivation
    -- * The Monad (for advanced use)
  , TracingRedex
  ) where

import TypedRedex.Core.Internal.Redex
import TypedRedex.Core.Internal.Logic
import Stream
import Control.Monad.State
import Control.Applicative
import Unsafe.Coerce (unsafeCoerce)
import TypedRedex.Utils.Redex (flatteningUnify, occursCheck, L, Var', prettyLogic)

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
      , derivArgs :: [String]         -- ^ Arguments (pretty-printed)
      , derivChildren :: [Derivation] -- ^ Premises (sub-derivations)
      }
  | Leaf String [String]              -- ^ Axiom with arguments
  deriving (Show, Eq)

-- | Pretty-print a derivation tree in paper style.
--
-- Renders premises horizontally above the inference line:
--
-- @
-- Γ ⊢ e1 ⇒ A → B   Γ ⊢ e2 ⇐ A
-- ──────────────────────────── [⇒App]
--        Γ ⊢ e1 e2 ⇒ B
-- @
prettyDerivation :: Derivation -> String
prettyDerivation d = unlines $ renderDeriv d
  where
    renderDeriv :: Derivation -> [String]
    renderDeriv (Leaf name _) = [name]
    renderDeriv (Deriv "top" _ children) =
      case children of
        [c] -> renderDeriv c
        cs -> concatMap renderDeriv cs
    renderDeriv (Deriv name args children) =
      let conclusion = formatConclusion name args
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

    formatConclusion :: String -> [String] -> String
    formatConclusion "step" [a, b] = a ++ " ⟶ " ++ b
    formatConclusion "value" [a] = "value(" ++ a ++ ")"
    formatConclusion "subst0" [body, arg, result] = "[" ++ arg ++ "/0]" ++ body ++ " = " ++ result
    formatConclusion "synth" [ctx, e, ty] = ctx ++ " ⊢ " ++ e ++ " ⇒ " ++ ty
    formatConclusion "check" [ctx, e, ty] = ctx ++ " ⊢ " ++ e ++ " ⇐ " ++ ty
    formatConclusion "lookup" [ctx, n, ty] = ctx ++ "(" ++ n ++ ") = " ++ ty
    formatConclusion name [] = name
    formatConclusion name [a, b] | name `elem` ["β", "app-L", "app-R", "succ", "pred", "pred-zero", "pred-succ", "ifz", "ifz-zero", "ifz-succ", "fix"] =
      a ++ " ⟶ " ++ b
    formatConclusion name args = name ++ "(" ++ intercalate ", " args ++ ")"

    intercalate :: String -> [String] -> String
    intercalate _ [] = ""
    intercalate _ [x] = x
    intercalate sep (x:xs) = x ++ sep ++ intercalate sep xs

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

type VarRepr = Int

-- | A frame in the derivation stack.
--
-- When we enter a rule, we push a frame. As premises are proved,
-- their derivations are added to frameChildren. When the rule completes,
-- we pop the frame and build a Derivation node.
data DerivFrame = DerivFrame
  { frameName     :: String        -- ^ Rule name
  , frameArgs     :: [String]      -- ^ Pretty-printed arguments
  , frameChildren :: [Derivation]  -- ^ Accumulated premise derivations
  }
  deriving (Show)

-- | Complete state for the tracing interpreter.
data TracingState s = TracingState
  { tsSubst      :: forall t. RVar (TracingRedex s) t -> Maybe t  -- ^ Substitution
  , tsNextVar    :: VarRepr                                        -- ^ Fresh var counter
  , tsDerivStack :: [DerivFrame]                                   -- ^ Derivation stack
  }

emptyState :: TracingState s
emptyState = TracingState
  { tsSubst = \v -> error $ "Invalid variable " ++ show (varToInt v)
  , tsNextVar = 0
  , tsDerivStack = [DerivFrame "top" [] []]  -- Start with top-level frame
  }

varToInt :: RVar (TracingRedex s) t -> Int
varToInt (TVar n) = n

readSubst :: RVar (TracingRedex s) a -> TracingState s -> Maybe a
readSubst v s = tsSubst s v

updateSubst :: RVar (TracingRedex s) a -> Maybe a -> TracingState s -> TracingState s
updateSubst v a s = s { tsSubst = \v' -> if varEq' v v' then unsafeCoerce a else tsSubst s v' }
  where
    varEq' (TVar a') (TVar b) = a' == b

succVar :: TracingState s -> TracingState s
succVar s = s { tsNextVar = succ (tsNextVar s) }

-- | Push a new derivation frame onto the stack.
pushFrame :: String -> [String] -> TracingState s -> TracingState s
pushFrame name args s = s { tsDerivStack = DerivFrame name args [] : tsDerivStack s }

-- | Pop frame and create derivation, add to parent frame.
popFrame :: TracingState s -> TracingState s
popFrame s = case tsDerivStack s of
  (current:parent:rest) ->
    let deriv = Deriv (frameName current) (frameArgs current) (reverse $ frameChildren current)
        parent' = parent { frameChildren = deriv : frameChildren parent }
    in s { tsDerivStack = parent' : rest }
  _ -> s  -- At top level, don't pop

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

  -- | Allocate fresh variables (same as SubstRedex)
  fresh_ FreshVar k = do
    v <- TVar <$> gets tsNextVar
    modify $ succVar . updateSubst v Nothing
    k v

  fresh_ (ArgVar x) k = do
    v <- TVar <$> gets tsNextVar
    modify $ succVar . updateSubst v (Just x)
    k v

  -- | Unification (same as SubstRedex)
  unify = flatteningUnify unif
    where
      unif v y
        | occursCheck v y = empty
        | otherwise = do
            x <- gets (readSubst v)
            maybe (modify $ updateSubst v (Just y)) (unify y) x

  -- | Display variable
  displayVar (TVar v) = "x" ++ show v

  -- | Suspend for fair interleaving
  suspend (TracingRedex r) = TracingRedex $ mapStateT Immature r

  -- | Custom call_ that handles derivation frame management.
  --
  -- 1. Push frame with relation name and args
  -- 2. Execute body
  -- 3. Pop frame and build derivation
  call_ Opaque rel = do
    modify $ pushFrame (relName rel) (relArgs rel)
    suspend (relBody rel)
    modify popFrame

  call_ Transparent rel = do
    modify $ pushFrame (relName rel) (relArgs rel)
    relBody rel
    modify popFrame

--------------------------------------------------------------------------------
-- RedexStructure Instance (Derivation Tracking)
--------------------------------------------------------------------------------

instance RedexStructure (TracingRedex s) where
  -- | Push a new derivation frame when entering a rule
  onRuleEnter name args = modify $ pushFrame name args

  -- | Pop frame and build derivation when exiting a rule
  onRuleExit _ = modify popFrame

  -- | Wrap premise call (default: just run body)
  -- Premises are tracked automatically via the call/popFrame mechanism
  withPremise _ _ = id

instance EqVar (TracingRedex s) where
  varEq (TVar a) (TVar b) = a == b

instance RedexEval (TracingRedex s) where
  derefVar v = do
    x <- gets (readSubst v)
    case x of
      Nothing -> error $ "Unbound variable: " ++ displayVar v
      Just val -> evalLogic val
    where
      evalLogic :: LogicType a => L a (TracingRedex s) -> TracingRedex s a
      evalLogic (Free v') = derefVar v'
      evalLogic (Ground r) = derefVal evalLogic r

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
runTracingRedex (TracingRedex r) = fmap extractDeriv $ runStateT r emptyState
  where
    extractDeriv (result, st) =
      let deriv = case tsDerivStack st of
            [frame] -> case frameChildren frame of
              [d] -> d
              ds -> Deriv "top" [] (reverse ds)
            (frame:_) -> Deriv (frameName frame) (frameArgs frame) (reverse $ frameChildren frame)
            [] -> Leaf "?" []
      in (result, deriv)

-- | Alias for 'runTracingRedex'.
runWithDerivation :: (forall s. TracingRedex s a) -> Stream (a, Derivation)
runWithDerivation = runTracingRedex
