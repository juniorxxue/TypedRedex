{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Shallow.Interpreters.SubstKanrenFresh
  ( runSubstKanrenFresh
  , Stream
  , takeS
  , takeWhileS
  ) where

import Shallow.Core.Internal.Kanren
import Shallow.Core.Internal.Logic
import Stream
import Control.Monad.State
import Control.Applicative (Alternative)
import Unsafe.Coerce (unsafeCoerce)
import Unbound.Generics.LocallyNameless (FreshMT, Fresh, runFreshMT)

type VarRepr = Int
type V s t = KVar (SubstKanrenFresh s) t

data Subst s = Subst
  { subst :: forall t. V s t -> Maybe t
  , nextVar :: VarRepr
  }

emptySubst :: Subst s
emptySubst = Subst
  { subst = \v -> error $ "Invalid variable " ++ displayVar v
  , nextVar = toEnum 0
  }

readSubst :: V s a -> Subst s -> Maybe a
readSubst v s = subst s v

updateSubst :: V s a -> Maybe a -> Subst s -> Subst s
updateSubst v a s = s { subst = \v' -> if v `varEq` v' then unsafeCoerce a else subst s v' }

succVar :: Subst s -> Subst s
succVar s = s { nextVar = succ (nextVar s) }

-- ============================================================================
-- SubstKanrenFresh: SubstKanren + Fresh
-- ============================================================================
-- Stack FreshMT on top of StateT/Stream to get Fresh capability

newtype SubstKanrenFresh s a = SubstKanrenFresh
  { unSubstKanrenFresh :: FreshMT (StateT (Subst s) Stream) a
  }
  deriving (Functor, Applicative, Alternative, Monad, Fresh)

type R s = SubstKanrenFresh s

instance MonadState (Subst s) (R s) where
  state f = SubstKanrenFresh $ lift $ state f

readVar :: V s t -> R s (Maybe t)
readVar v = gets $ readSubst v

makeVar :: Maybe (Logic a (KVar (R s))) -> R s (V s (Logic a (KVar (R s))))
makeVar x = do
  v <- SVar <$> gets nextVar
  modify $ succVar . updateSubst v x
  return v

-- ============================================================================
-- Kanren instance with Fresh support
-- ============================================================================

instance Kanren (R s) where

  newtype instance (KVar (R s)) t = SVar VarRepr deriving (Functor, Show)

  fresh_ FreshVar   = (makeVar Nothing >>=)
  fresh_ (ArgVar x) = (makeVar (Just x) >>=)

  unify = flatteningUnify unif
    where
      unif v y
        | occursCheck v y = empty
        | otherwise = do
            x <- readVar v
            maybe (modify $ updateSubst v (Just y)) (unify y) x

  call_ Opaque (Relation _ (SubstKanrenFresh r)) =
    SubstKanrenFresh $ lift $ mapStateT Immature $ runFreshMT r
  call_ Transparent (Relation _ r) = r

  displayVar (SVar v) = "x" ++ show v

instance KanrenEval (R s) where

  derefVar v = do
    x <- gets $ readSubst v
    maybe (error $ "Unbound variable: " ++ displayVar v) eval x

instance EqVar (R s) where
  varEq (SVar a) (SVar b) = a == b

-- ============================================================================
-- Utilities (need to be adapted for monadic LogicType)
-- ============================================================================

-- Type aliases
type Var' a rel = KVar rel (Logic a (KVar rel))
type L a rel = Logic a (KVar rel)

flatteningUnify :: (Alternative rel, Kanren rel, LogicType a) =>
  (forall a'. (LogicType a') => Var' a' rel -> L a' rel -> rel ()) ->
  L a rel -> L a rel -> rel ()
flatteningUnify unifyVar (Free a) b = unifyVar a b
flatteningUnify unifyVar a (Free b) = unifyVar b a
flatteningUnify unifyVar (Ground a) (Ground b) = unifyVal (flatteningUnify unifyVar) a b

eval :: (KanrenEval rel, LogicType a) => L a rel -> rel a
eval (Free v) = derefVar v
eval (Ground x) = derefVal eval x

occursCheck :: (LogicType b, EqVar rel) => Var' a rel -> L b rel -> Bool
occursCheck x (Free y) = x `varEq` y
occursCheck x (Ground y) = let (_, ys) = quote y in any (\(Field _ y') -> occursCheck x y') ys

-- ============================================================================
-- Run function
-- ============================================================================

runSubstKanrenFresh :: (forall s. R s t) -> Stream t
runSubstKanrenFresh (SubstKanrenFresh r) = evalStateT (runFreshMT r) emptySubst
