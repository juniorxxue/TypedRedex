{-# LANGUAGE TypeFamilies, DeriveFunctor, Rank2Types, GeneralisedNewtypeDeriving, TypeSynonymInstances, MultiParamTypeClasses, FlexibleContexts #-}

-- | SubstRedex: A substitution-based interpreter for TypedRedex
--
-- This is the standard "eval" interpreter that executes logic programs
-- via substitutions and backtracking streams.

module TypedRedex.Interp.Subst
  ( runSubstRedex
  , Stream
  , takeS
  , takeWhileS
  ) where

import TypedRedex.Core.Internal.Redex
import TypedRedex.Core.Internal.Unify (flatteningUnify, occursCheck)
import TypedRedex.Core.Internal.SubstCore (VarRepr, displayVarInt)
import TypedRedex.DSL.Fresh (LTerm, LVar)
import TypedRedex.Interp.Run (eval)
import TypedRedex.Interp.Stream
import Control.Monad.State
import Unsafe.Coerce (unsafeCoerce)

type V s t = RVar (SubstRedex s) t

-- | Substitution state for SubstRedex.
data Subst s = Subst { subst :: forall t. V s t -> Maybe t, nextVar :: VarRepr }

emptySubst :: Subst s
emptySubst = Subst { subst = \v -> error $ "Invalid variable " ++ displayVar v, nextVar = 0 }

readSubst :: V s a -> Subst s -> Maybe a
readSubst v s = subst s v

updateSubst :: V s a -> Maybe a -> Subst s -> Subst s
updateSubst v a s = s { subst = \v' -> if v `varEq` v' then unsafeCoerce a else subst s v' }

succVar :: Subst s -> Subst s
succVar s = s { nextVar = succ (nextVar s) }

newtype SubstRedex s a = SubstRedex (StateT (Subst s) Stream a)
  deriving (Functor, Applicative, Alternative, Monad)

type R s = SubstRedex s

instance MonadState (Subst s) (R s) where
    state = SubstRedex . state

readVar :: V s t -> R s (Maybe t)
readVar v = gets $ readSubst v

makeVar :: Maybe (LTerm a (R s)) -> R s (LVar a (R s))
makeVar x = do
    v <- SVar <$> gets nextVar
    modify $ succVar . updateSubst v x
    return v

instance Redex (R s) where
    newtype instance (RVar (R s)) t = SVar VarRepr deriving (Functor, Show)

    fresh_ FreshVar   = (makeVar Nothing >>=)
    fresh_ (ArgVar x) = (makeVar (Just x) >>=)

    unify = flatteningUnify unif
        where
            unif v y | occursCheck v y = empty
                     | otherwise = do
                        x <- readVar v
                        maybe (modify $ updateSubst v (Just y))
                              (unify y)
                              x

    displayVar (SVar v) = displayVarInt v

    suspend (SubstRedex r) = SubstRedex $ mapStateT Immature r

instance RedexEval (R s) where
    derefVar v = do
        x <- gets $ readSubst v
        maybe (error $ "Unbound variable: " ++ displayVar v) eval x

instance RedexNeg (R s) where
  -- | Negation-as-failure: succeed if goal has no solutions
  neg goal = do
      s0 <- get
      let SubstRedex goalComp = goal
          answerStream = execStateT goalComp s0
      case firstAnswer answerStream of
        Nothing -> pure ()
        Just _  -> empty
    where
      firstAnswer :: Stream a -> Maybe a
      firstAnswer Empty = Nothing
      firstAnswer (Mature a _) = Just a
      firstAnswer (Immature rest) = firstAnswer rest

instance EqVar (R s) where
    varEq (SVar a) (SVar b) = a == b

runSubstRedex :: (forall s. R s t) -> Stream t
runSubstRedex (SubstRedex r) = evalStateT r emptySubst
