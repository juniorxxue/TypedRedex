{-# LANGUAGE TypeFamilies, DeriveFunctor, Rank2Types, GeneralisedNewtypeDeriving, TypeSynonymInstances, MultiParamTypeClasses, FlexibleContexts, ExistentialQuantification, ScopedTypeVariables #-}

-- | SubstRedex: A substitution-based interpreter for TypedRedex
--
-- This is the standard "eval" interpreter that executes logic programs
-- via substitutions and backtracking streams.

module TypedRedex.Interp.Subst
  ( runSubstRedex
  , Stream
  , takeS
  , takeWhileS
    -- * Fresh Name Generation
  , RedexFresh(..)
    -- * Hash Constraints
  , RedexHash(..)
  ) where

import TypedRedex.Core.Internal.Redex
import TypedRedex.Core.Internal.Logic (Logic(..), LogicType(..), reify)
import TypedRedex.Core.Internal.Unify (flatteningUnify, occursCheck)
import TypedRedex.Core.Internal.SubstCore (VarRepr, displayVarInt)
import TypedRedex.DSL.Fresh (LTerm, LVar)
import TypedRedex.Interp.Run (eval)
import TypedRedex.Interp.Stream
import TypedRedex.Nominal.Nom (NominalAtom)
import TypedRedex.Nominal.Hash (Hash(..), RedexHash(..))
import Control.Monad.State
import Control.Monad (guard, forM_)
import Control.Applicative (empty)
import Unsafe.Coerce (unsafeCoerce)

type V s t = RVar (SubstRedex s) t

-- | An existentially wrapped hash constraint: name # term
-- Used to store heterogeneous constraints in the constraint store.
data HashConstraint s = forall name term.
  (NominalAtom name, LogicType name, LogicType term, Hash name term) =>
  HashConstraint (LTerm name (SubstRedex s)) (LTerm term (SubstRedex s))

-- | Substitution state for SubstRedex.
data Subst s = Subst
  { subst :: forall t. V s t -> Maybe t
  , nextVar :: VarRepr
  , freshCounter :: !Int  -- ^ Counter for fresh nominal atoms
  , hashConstraints :: [HashConstraint s]  -- ^ Lazy hash constraints: name # term
  }

emptySubst :: Subst s
emptySubst = Subst
  { subst = \v -> error $ "Invalid variable " ++ displayVar v
  , nextVar = 0
  , freshCounter = 0
  , hashConstraints = []
  }

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
                        case x of
                          Nothing -> do
                            modify $ updateSubst v (Just y)
                            recheckHashConstraints  -- Check hash constraints after binding
                          Just x' -> unify y x'

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

--------------------------------------------------------------------------------
-- Fresh Name Generation (Generic)
--------------------------------------------------------------------------------

-- | Typeclass for interpreters that support fresh name generation.
--
-- Users build their own nominal atom generators using 'freshInt':
--
-- @
-- freshNom :: RedexFresh rel => rel Nom
-- freshNom = Nom \<$\> freshInt
--
-- freshTyNom :: RedexFresh rel => rel TyNom
-- freshTyNom = TyNom \<$\> freshInt
-- @
class Redex rel => RedexFresh rel where
  -- | Generate a fresh unique integer.
  freshInt :: rel Int

instance RedexFresh (R s) where
  freshInt = do
    s <- get
    let n = freshCounter s
    put s { freshCounter = n + 1 }
    pure n

--------------------------------------------------------------------------------
-- Hash Constraints
--------------------------------------------------------------------------------

-- | Walk a logic term to its root (following variable bindings).
walkL :: LogicType a => LTerm a (R s) -> R s (LTerm a (R s))
walkL (Ground r) = pure (Ground r)
walkL (Free v) = do
  mx <- readVar v
  case mx of
    Nothing -> pure (Free v)  -- Unbound variable
    Just lt -> walkL lt       -- Follow the binding

-- | Check if a logic term is ground (no unbound variables at the root).
isGroundL :: LogicType a => LTerm a (R s) -> R s (Maybe a)
isGroundL lt = do
  lt' <- walkL lt
  case lt' of
    Ground r -> pure (reify r)
    Free _   -> pure Nothing

-- | Add a hash constraint to the constraint store.
addHashConstraint :: (NominalAtom name, LogicType name, LogicType term, Hash name term)
                  => LTerm name (R s) -> LTerm term (R s) -> R s ()
addHashConstraint nameL termL = modify $ \s ->
  s { hashConstraints = HashConstraint nameL termL : hashConstraints s }

-- | Check a single hash constraint. Returns True if satisfied or deferred.
checkHashConstraint :: HashConstraint s -> R s ()
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
recheckHashConstraints :: R s ()
recheckHashConstraints = do
  constraints <- gets hashConstraints
  -- Clear the constraint store before re-checking
  modify $ \s -> s { hashConstraints = [] }
  -- Re-check each constraint (will re-add if still not ground)
  forM_ constraints checkHashConstraint

instance RedexHash (R s) where
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
