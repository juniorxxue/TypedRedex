{-# LANGUAGE TypeFamilies, DeriveFunctor, Rank2Types, GeneralisedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances #-}
module Shallow.Interpreters.TracingKanren
  ( runTracingKanren
  , runWithDerivation
  , Derivation(..)
  , prettyDerivation
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
  = Deriv String [Derivation]  -- Rule name and sub-derivations (premises)
  | Leaf String                 -- Axiom or base case
  deriving (Show, Eq)

-- | Pretty-print a derivation tree
prettyDerivation :: Derivation -> String
prettyDerivation d = unlines $ go "" d
  where
    go prefix (Leaf name) = [prefix ++ "── " ++ name]
    go prefix (Deriv name []) = [prefix ++ "── " ++ name]
    go prefix (Deriv name children) =
      (prefix ++ "┬─ " ++ name) : concatMap (go (prefix ++ "│  ")) (init children)
        ++ go (prefix ++ "   ") (last children)

--------------------------------------------------------------------------------
-- Tracing Kanren State
--------------------------------------------------------------------------------

type VarRepr = Int

data TracingState s = TracingState
  { tsSubst :: forall t. KVar (TracingKanren s) t -> Maybe t
  , tsNextVar :: VarRepr
  , tsDerivStack :: [[Derivation]]  -- Stack of derivation lists (for nested calls)
  , tsCurrentRule :: Maybe String   -- Current rule being evaluated
  }

emptyState :: TracingState s
emptyState = TracingState
  { tsSubst = \v -> error $ "Invalid variable " ++ show (varToInt v)
  , tsNextVar = 0
  , tsDerivStack = [[]]  -- Start with one empty frame
  , tsCurrentRule = Nothing
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
pushFrame :: TracingState s -> TracingState s
pushFrame s = s { tsDerivStack = [] : tsDerivStack s }

-- Pop frame and create derivation, add to parent frame
popFrame :: String -> TracingState s -> TracingState s
popFrame ruleName s = case tsDerivStack s of
  (current:parent:rest) ->
    let deriv = Deriv ruleName (reverse current)
    in s { tsDerivStack = (deriv : parent) : rest }
  [current] ->
    -- At top level, just wrap it
    let deriv = Deriv ruleName (reverse current)
    in s { tsDerivStack = [[deriv]] }
  [] -> s  -- Shouldn't happen

-- Add a leaf derivation to current frame
addLeaf :: String -> TracingState s -> TracingState s
addLeaf name s = case tsDerivStack s of
  (current:rest) -> s { tsDerivStack = (Leaf name : current) : rest }
  [] -> s { tsDerivStack = [[Leaf name]] }

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

  call_ Opaque (Relation name body) = do
    -- Push new frame before executing
    modify pushFrame
    -- Execute the body (with Immature for fairness)
    TracingKanren $ mapStateT Immature $ case body of
      TracingKanren r -> r
    -- Pop frame and record derivation
    modify (popFrame name)

  call_ Transparent (Relation name body) = do
    modify pushFrame
    body
    modify (popFrame name)

  displayVar (TVar v) = "x" ++ show v

  onRelationCall _ _ = pure ()  -- We track via call_ instead

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
            [[d]] -> d
            [ds] -> Deriv "top" (reverse ds)
            (d:_) -> Deriv "top" (reverse d)
            [] -> Leaf "?"
      in (result, deriv)

-- | Helper to run and extract derivation (same as runTracingKanren)
runWithDerivation :: (forall s. TracingKanren s a) -> Stream (a, Derivation)
runWithDerivation = runTracingKanren
