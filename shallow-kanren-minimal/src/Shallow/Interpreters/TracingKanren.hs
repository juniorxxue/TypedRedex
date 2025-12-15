{-# LANGUAGE TypeFamilies, DeriveFunctor, Rank2Types, GeneralisedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances #-}
module Shallow.Interpreters.TracingKanren
  ( runTracingKanren
  , runWithDerivation
  , Derivation(..)
  , prettyDerivation
  , substInDerivation
  , TracingKanren
  ) where

import Shallow.Core.Internal.Kanren
import Shallow.Core.Internal.Logic
import Stream
import Control.Monad.State
import Control.Applicative
import Unsafe.Coerce (unsafeCoerce)
import Shallow.Utils.Kanren (flatteningUnify, occursCheck, L, Var', prettyLogic)

-- | Derivation tree representing a proof
data Derivation
  = Deriv
      { derivRule :: String           -- Rule name
      , derivArgs :: [String]         -- Arguments to the relation
      , derivChildren :: [Derivation] -- Sub-derivations (premises)
      }
  | Leaf String [String]              -- Axiom with arguments
  deriving (Show, Eq)

-- | Pretty-print a derivation tree in paper style with horizontal premises
-- Renders premises side-by-side above the inference line
prettyDerivation :: Derivation -> String
prettyDerivation d = unlines $ renderDeriv d
  where
    -- Render a derivation as a list of lines (a rectangular block)
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
               -- Center the conclusion under the line
               concPad = (lineWidth - concWidth) `div` 2
               paddedConc = replicate concPad ' ' ++ conclusion
           in combined ++ [line, paddedConc]

    -- Place two blocks side by side with spacing
    sideBySide :: [String] -> [String] -> [String]
    sideBySide left right =
      let leftWidth = if null left then 0 else maximum (map length left)
          leftHeight = length left
          rightHeight = length right
          maxHeight = max leftHeight rightHeight
          -- Pad left block to uniform width and height
          padLeft = replicate (maxHeight - leftHeight) (replicate leftWidth ' ')
                    ++ map (padRight leftWidth) left
          -- Pad right block to height
          padRightBlock = replicate (maxHeight - rightHeight) "" ++ right
          spacing = "   "  -- 3 spaces between premises
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

-- | Substitute a variable in a derivation with an actual value
substInDerivation :: String -> String -> Derivation -> Derivation
substInDerivation var val (Leaf name args) = Leaf name (map subst args)
  where subst s = if s == var then val else s
substInDerivation var val (Deriv name args children) =
  Deriv name (map subst args) (map (substInDerivation var val) children)
  where subst s = if s == var then val else s

--------------------------------------------------------------------------------
-- Tracing Kanren State
--------------------------------------------------------------------------------

type VarRepr = Int

-- | A frame in the derivation stack
data DerivFrame = DerivFrame
  { frameName :: String
  , frameArgs :: [String]
  , frameChildren :: [Derivation]
  }
  deriving (Show)

data TracingState s = TracingState
  { tsSubst :: forall t. KVar (TracingKanren s) t -> Maybe t
  , tsNextVar :: VarRepr
  , tsDerivStack :: [DerivFrame]  -- Stack of derivation frames
  }

emptyState :: TracingState s
emptyState = TracingState
  { tsSubst = \v -> error $ "Invalid variable " ++ show (varToInt v)
  , tsNextVar = 0
  , tsDerivStack = [DerivFrame "top" [] []]
  }

varToInt :: KVar (TracingKanren s) t -> Int
varToInt (TVar n) = n

readSubst :: KVar (TracingKanren s) a -> TracingState s -> Maybe a
readSubst v s = tsSubst s v

updateSubst :: KVar (TracingKanren s) a -> Maybe a -> TracingState s -> TracingState s
updateSubst v a s = s { tsSubst = \v' -> if varEq' v v' then unsafeCoerce a else tsSubst s v' }
  where
    varEq' (TVar a') (TVar b) = a' == b

succVar :: TracingState s -> TracingState s
succVar s = s { tsNextVar = succ (tsNextVar s) }

-- Push a new derivation frame
pushFrame :: String -> [String] -> TracingState s -> TracingState s
pushFrame name args s = s { tsDerivStack = DerivFrame name args [] : tsDerivStack s }

-- Pop frame and create derivation, add to parent frame
popFrame :: TracingState s -> TracingState s
popFrame s = case tsDerivStack s of
  (current:parent:rest) ->
    let deriv = Deriv (frameName current) (frameArgs current) (reverse $ frameChildren current)
        parent' = parent { frameChildren = deriv : frameChildren parent }
    in s { tsDerivStack = parent' : rest }
  _ -> s  -- At top level, don't pop

-- Add a completed derivation to current frame
addDerivation :: Derivation -> TracingState s -> TracingState s
addDerivation d s = case tsDerivStack s of
  (current:rest) -> s { tsDerivStack = current { frameChildren = d : frameChildren current } : rest }
  [] -> s

--------------------------------------------------------------------------------
-- Tracing Kanren Monad
--------------------------------------------------------------------------------

newtype TracingKanren s a = TracingKanren (StateT (TracingState s) Stream a)
  deriving (Functor, Applicative, Monad)

instance Alternative (TracingKanren s) where
  empty = TracingKanren $ StateT $ \_ -> Empty
  TracingKanren a <|> TracingKanren b = TracingKanren $ StateT $ \s ->
    runStateT a s <|> runStateT b s

instance MonadState (TracingState s) (TracingKanren s) where
  state = TracingKanren . state

--------------------------------------------------------------------------------
-- Kanren Instance
--------------------------------------------------------------------------------

instance Kanren (TracingKanren s) where
  newtype KVar (TracingKanren s) t = TVar VarRepr
    deriving (Functor, Show)

  fresh_ FreshVar k = do
    v <- TVar <$> gets tsNextVar
    modify $ succVar . updateSubst v Nothing
    k v

  fresh_ (ArgVar x) k = do
    v <- TVar <$> gets tsNextVar
    modify $ succVar . updateSubst v (Just x)
    k v

  unify = flatteningUnify unif
    where
      unif v y
        | occursCheck v y = empty
        | otherwise = do
            x <- gets (readSubst v)
            maybe (modify $ updateSubst v (Just y)) (unify y) x

  -- call_ executes body (which will push frame via onRelationCall), then pops
  call_ Opaque (Relation _ body) = do
    -- Execute the body - onRelationCall inside will push the frame
    TracingKanren $ mapStateT Immature $ case body of
      TracingKanren r -> r
    -- Pop frame after body completes
    modify popFrame

  call_ Transparent (Relation _ body) = do
    body
    modify popFrame

  displayVar (TVar v) = "x" ++ show v

  -- This is called at the START of each relation body - push frame here
  onRelationCall name args = do
    modify $ pushFrame name args

instance EqVar (TracingKanren s) where
  varEq (TVar a) (TVar b) = a == b

instance KanrenEval (TracingKanren s) where
  derefVar v = do
    x <- gets (readSubst v)
    case x of
      Nothing -> error $ "Unbound variable: " ++ displayVar v
      Just val -> evalLogic val
    where
      evalLogic :: LogicType a => L a (TracingKanren s) -> TracingKanren s a
      evalLogic (Free v') = derefVar v'
      evalLogic (Ground r) = derefVal evalLogic r

--------------------------------------------------------------------------------
-- Running
--------------------------------------------------------------------------------

-- | Run a tracing computation and return results with derivations
runTracingKanren :: (forall s. TracingKanren s a) -> Stream (a, Derivation)
runTracingKanren (TracingKanren r) = fmap extractDeriv $ runStateT r emptyState
  where
    extractDeriv (result, st) =
      let deriv = case tsDerivStack st of
            [frame] -> case frameChildren frame of
              [d] -> d
              ds -> Deriv "top" [] (reverse ds)
            (frame:_) -> Deriv (frameName frame) (frameArgs frame) (reverse $ frameChildren frame)
            [] -> Leaf "?" []
      in (result, deriv)

-- | Helper to run and extract derivation (same as runTracingKanren)
runWithDerivation :: (forall s. TracingKanren s a) -> Stream (a, Derivation)
runWithDerivation = runTracingKanren
