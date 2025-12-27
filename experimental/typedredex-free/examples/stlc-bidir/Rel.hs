{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ExistentialQuantification #-}

-- | Minimal Logic Monad for demonstration.
--
-- A simple substitution-based implementation for demonstrating
-- the free monad interpreters. Uses a stream-based approach.
module Rel
  ( Rel
  , runRel
  , runRelN
  ) where

import Control.Applicative (Alternative(..))
import Control.Monad (MonadPlus(..))
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.Typeable (Typeable, cast)

import TypedRedex.Free.Logic

--------------------------------------------------------------------------------
-- Substitution
--------------------------------------------------------------------------------

-- | Existential wrapper for any logic term
data SomeTerm = forall a. (LogicType a, Typeable a) => SomeTerm (Logic a (RVar Rel))

-- | Substitution: maps variable IDs to terms
type Subst = IntMap SomeTerm

-- | Empty substitution
emptySubst :: Subst
emptySubst = IM.empty

--------------------------------------------------------------------------------
-- The Rel Monad (Stream-based)
--------------------------------------------------------------------------------

-- | State: next var ID and substitution
data State = State
  { stNextVar :: !Int
  , stSubst   :: !Subst
  }

emptyState :: State
emptyState = State 0 emptySubst

-- | Logic monad as a function from state to stream of (result, state)
newtype Rel a = Rel { unRel :: State -> [(a, State)] }

instance Functor Rel where
  fmap f (Rel m) = Rel $ \s -> [(f a, s') | (a, s') <- m s]

instance Applicative Rel where
  pure a = Rel $ \s -> [(a, s)]
  Rel mf <*> Rel ma = Rel $ \s ->
    [(f a, s'') | (f, s') <- mf s, (a, s'') <- ma s']

instance Monad Rel where
  Rel m >>= f = Rel $ \s ->
    concat [unRel (f a) s' | (a, s') <- m s]

instance Alternative Rel where
  empty = Rel $ \_ -> []
  Rel m1 <|> Rel m2 = Rel $ \s -> interleave (m1 s) (m2 s)
    where
      interleave [] ys = ys
      interleave (x:xs) ys = x : interleave ys xs

instance MonadPlus Rel

--------------------------------------------------------------------------------
-- Redex Instance
--------------------------------------------------------------------------------

instance Redex Rel where
  -- Variable is just an Int ID
  newtype RVar Rel a = RelVar Int
    deriving (Eq)

  fresh_ _ k = Rel $ \s ->
    let varId = stNextVar s
        s' = s { stNextVar = varId + 1 }
    in unRel (k (Var (RelVar varId))) s'

  unify t1 t2 = unifyLogic t1 t2

  displayVar (RelVar n) = "x" ++ show n

  suspend m = m  -- No suspension in this simple impl

instance Functor (RVar Rel) where
  fmap _ (RelVar n) = RelVar n

--------------------------------------------------------------------------------
-- Unification
--------------------------------------------------------------------------------

-- | Walk a term following substitution
walk :: forall a. (LogicType a, Typeable a)
     => Subst -> Logic a (RVar Rel) -> Logic a (RVar Rel)
walk subst (Free (Var (RelVar n))) =
  case IM.lookup n subst of
    Nothing -> Free (Var (RelVar n))
    Just (SomeTerm t) ->
      case cast t of
        Just t' -> walk subst t'
        Nothing -> Free (Var (RelVar n))  -- Type mismatch, keep as var
walk _ t = t

-- | Extend substitution
extendSubst :: (LogicType a, Typeable a)
            => Int -> Logic a (RVar Rel) -> Subst -> Subst
extendSubst n t subst = IM.insert n (SomeTerm t) subst

-- | Unify two logic terms
unifyLogic :: forall a. (LogicType a, Typeable a)
           => Logic a (RVar Rel) -> Logic a (RVar Rel) -> Rel ()
unifyLogic t1 t2 = Rel $ \s ->
  let subst = stSubst s
      t1' = walk subst t1
      t2' = walk subst t2
  in unifyWalked s t1' t2'
  where
    unifyWalked :: State -> Logic a (RVar Rel) -> Logic a (RVar Rel) -> [((), State)]
    unifyWalked s (Free (Var (RelVar n1))) (Free (Var (RelVar n2)))
      | n1 == n2 = [((), s)]
    unifyWalked s (Free (Var (RelVar n))) t =
      [((), s { stSubst = extendSubst n t (stSubst s) })]
    unifyWalked s t (Free (Var (RelVar n))) =
      [((), s { stSubst = extendSubst n t (stSubst s) })]
    unifyWalked s (Ground r1) (Ground r2) =
      unRel (unifyVal @a unifyLogic r1 r2) s

--------------------------------------------------------------------------------
-- RedexNeg Instance
--------------------------------------------------------------------------------

instance RedexNeg Rel where
  neg goal = Rel $ \s ->
    case unRel goal s of
      [] -> [((), s)]  -- Goal failed, negation succeeds
      _  -> []         -- Goal succeeded, negation fails

--------------------------------------------------------------------------------
-- Running
--------------------------------------------------------------------------------

-- | Run a Rel computation and get all results
runRel :: Rel a -> [a]
runRel m = map fst $ unRel m emptyState

-- | Run and get first N results
runRelN :: Int -> Rel a -> [a]
runRelN n m = take n $ runRel m
