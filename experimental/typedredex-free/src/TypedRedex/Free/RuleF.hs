{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE StandaloneKindSignatures #-}

-- | Indexed Functor for Rule DSL Operations
--
-- This module defines 'RuleF', the indexed functor whose operations
-- form the basis of the free monad DSL.
--
-- = Operations
--
-- @
-- FreshF  : allocate a fresh logic variable
-- ConclF  : declare the conclusion pattern
-- PremF   : declare a premise
-- NegF    : declare negation-as-failure
-- LiftRelF: lift an arbitrary rel action
-- @
--
-- = Type-Level State Tracking
--
-- Each operation has a type that specifies its state transition:
--
-- @
-- FreshF :: RuleF ... ('St n steps c) ('St (n+1) steps c) ...
--           -- Allocates var n, increments counter
--
-- ConclF :: RuleF ... ('St n steps 'False) ('St n steps' 'True) ...
--           -- Declares conclusion, adds ConcStep to steps
-- @
module TypedRedex.Free.RuleF
  ( -- * The Indexed Functor
    RuleF(..)
    -- * Moded Terms
  , T(..)
  , ground
  , lift1, lift2, lift3
    -- * Argument Lists
  , TArgs(..)
  , ToLTermList(..)
  , LTermList(..)
  , captureArgs
    -- * Input/Output Variables
  , InputVars(..)
  , OutputVars(..)
    -- * Applied Judgments
  , AppliedM(..)
    -- * Re-exports
  , module TypedRedex.Free.Schedule
  ) where

import Data.Kind (Type)
import Data.Set (Set)
import qualified Data.Set as S
import GHC.TypeLits (Nat, Symbol, type (+))
import Data.Typeable (Typeable)

import TypedRedex.Logic (LogicType, Logic(..), Redex, RVar, CapturedTerm(..))
import TypedRedex.Free.Schedule

--------------------------------------------------------------------------------
-- Moded Terms
--------------------------------------------------------------------------------

-- | Term with type-level and runtime variable tracking
--
-- @vs@ is a type-level list of variable indices this term depends on
-- @a@ is the Haskell type
-- @rel@ is the interpreter type
data T (vs :: [Nat]) (a :: Type) (rel :: Type -> Type) = T
  { tVars :: Set Int       -- ^ Runtime variable IDs
  , tTerm :: Logic a (RVar rel)  -- ^ The underlying logic term
  }

-- | Wrap a ground term (no variables)
ground :: Logic a (RVar rel) -> T '[] a rel
ground t = T S.empty t

-- | Lift a unary function, preserving variable tracking
lift1 :: (Logic a (RVar rel) -> Logic b (RVar rel))
      -> T vs a rel -> T vs b rel
lift1 f (T vars x) = T vars (f x)

-- | Lift a binary function, merging variable sets
lift2 :: (Logic a (RVar rel) -> Logic b (RVar rel) -> Logic c (RVar rel))
      -> T vs1 a rel -> T vs2 b rel -> T (Union vs1 vs2) c rel
lift2 f (T vars1 x) (T vars2 y) = T (S.union vars1 vars2) (f x y)

-- | Lift a ternary function, merging variable sets
lift3 :: (Logic a (RVar rel) -> Logic b (RVar rel) -> Logic c (RVar rel) -> Logic d (RVar rel))
      -> T vs1 a rel -> T vs2 b rel -> T vs3 c rel
      -> T (Union vs1 (Union vs2 vs3)) d rel
lift3 f (T vars1 x) (T vars2 y) (T vars3 z) = T (S.unions [vars1, vars2, vars3]) (f x y z)

--------------------------------------------------------------------------------
-- Argument Lists
--------------------------------------------------------------------------------

-- | Typed argument list with var-set tracking
data TArgs (vss :: [[Nat]]) (ts :: [Type]) (rel :: Type -> Type) where
  ANil :: TArgs '[] '[] rel
  (:!) :: T vs a rel -> TArgs vss ts rel -> TArgs (vs ': vss) (a ': ts) rel

infixr 5 :!

-- | LTermList from typedredex-logic (simplified version here)
data LTermList (rel :: Type -> Type) (ts :: [Type]) where
  TNil :: LTermList rel '[]
  (:>) :: LogicType t => Logic t (RVar rel) -> LTermList rel ts -> LTermList rel (t ': ts)

infixr 5 :>

-- | Convert TArgs to LTermList (strip variable tracking)
class ToLTermList (vss :: [[Nat]]) (ts :: [Type]) where
  toLTermList :: TArgs vss ts rel -> LTermList rel ts

instance ToLTermList '[] '[] where
  toLTermList ANil = TNil

instance (LogicType t, ToLTermList vss ts) => ToLTermList (vs ': vss) (t ': ts) where
  toLTermList (t :! xs) = tTerm t :> toLTermList xs

--------------------------------------------------------------------------------
-- Input/Output Variable Extraction
--------------------------------------------------------------------------------

-- | Get runtime variable sets for input positions
class InputVars (ms :: [Mode]) (vss :: [[Nat]]) (ts :: [Type]) where
  inputVars :: ModeList ms -> TArgs vss ts rel -> Set Int

instance InputVars '[] '[] '[] where
  inputVars MNil ANil = S.empty

instance InputVars ms vss ts => InputVars ('I ': ms) (vs ': vss) (t ': ts) where
  inputVars (_ :* ms) (t :! ts) = S.union (tVars t) (inputVars ms ts)

instance InputVars ms vss ts => InputVars ('O ': ms) (vs ': vss) (t ': ts) where
  inputVars (_ :* ms) (_ :! ts) = inputVars ms ts

-- | Get runtime variable sets for output positions
class OutputVars (ms :: [Mode]) (vss :: [[Nat]]) (ts :: [Type]) where
  outputVars :: ModeList ms -> TArgs vss ts rel -> Set Int

instance OutputVars '[] '[] '[] where
  outputVars MNil ANil = S.empty

instance OutputVars ms vss ts => OutputVars ('I ': ms) (vs ': vss) (t ': ts) where
  outputVars (_ :* ms) (_ :! ts) = outputVars ms ts

instance OutputVars ms vss ts => OutputVars ('O ': ms) (vs ': vss) (t ': ts) where
  outputVars (_ :* ms) (t :! ts) = S.union (tVars t) (outputVars ms ts)

--------------------------------------------------------------------------------
-- Applied Judgments
--------------------------------------------------------------------------------

-- | Result of applying a moded judgment
--
-- Carries mode information at type and runtime level
data AppliedM (rel :: Type -> Type) (name :: Symbol) (modes :: [Mode]) (vss :: [[Nat]]) (ts :: [Type]) = AppliedM
  { amGoal    :: rel ()           -- ^ Goal to execute
  , amName    :: String           -- ^ Judgment name
  , amArgs    :: LTermList rel ts -- ^ Arguments
  , amReqVars :: Set Int          -- ^ Required variables (inputs)
  , amProdVars :: Set Int         -- ^ Produced variables (outputs)
  }

-- | Capture arguments as CapturedTerms for tracing
captureArgs :: LTermList rel ts -> [CapturedTerm rel]
captureArgs TNil = []
captureArgs (x :> xs) = CapturedTerm x : captureArgs xs

--------------------------------------------------------------------------------
-- The Indexed Functor
--------------------------------------------------------------------------------

-- | Indexed functor for rule DSL operations
--
-- Each constructor specifies:
-- * Input state (before operation)
-- * Output state (after operation)
-- * Result type
--
-- The type-level @steps@ list accumulates as operations are sequenced,
-- enabling compile-time schedule verification.
type RuleF :: (Type -> Type) -> [Type] -> St -> St -> Type -> Type
data RuleF (rel :: Type -> Type) (ts :: [Type]) (s :: St) (t :: St) (a :: Type) where

  -- | Allocate a fresh logic variable
  --
  -- @
  -- fresh :: RuleM ... ('St n steps c) ('St (n+1) steps c) (T '[n] a rel)
  -- @
  FreshF :: (LogicType a, Typeable a)
         => RuleF rel ts ('St n steps c) ('St (n + 1) steps c) (T '[n] a rel)

  -- | Declare the conclusion pattern
  --
  -- * Must be called exactly once (changes 'False to 'True)
  -- * Adds ConcStep to the steps list
  ConclF :: ( InputVars modes vss ts
            , OutputVars modes vss ts
            , ToLTermList vss ts
            )
         => AppliedM rel name modes vss ts
         -> RuleF rel ts
              ('St n steps 'False)
              ('St n (Snoc steps ('ConcStep name (ReqVars modes vss) (ProdVars modes vss))) 'True)
              ()

  -- | Declare a premise
  --
  -- Adds PremStep to the steps list
  PremF :: ( InputVars modes vss ts'
           , OutputVars modes vss ts'
           )
        => AppliedM rel name modes vss ts'
        -> RuleF rel ts
             ('St n steps c)
             ('St n (Snoc steps ('PremStep ('Goal name (ReqVars modes vss) (ProdVars modes vss)))) c)
             ()

  -- | Declare negation-as-failure
  --
  -- Adds NegStep to the steps list
  NegF :: ( InputVars modes vss ts'
          , OutputVars modes vss ts'
          )
       => AppliedM rel name modes vss ts'
       -> RuleF rel ts
            ('St n steps c)
            ('St n (Snoc steps ('NegStep (AllVars modes vss))) c)
            ()

  -- | Unification constraint (both must be ground)
  UnifyF :: (LogicType a, Typeable a)
         => T vs1 a rel
         -> T vs2 a rel
         -> RuleF rel ts
              ('St n steps c)
              ('St n (Snoc steps ('PremStep ('Goal "==" (Union vs1 vs2) '[]))) c)
              ()

  -- | Disequality constraint
  NeqF :: (LogicType a, Typeable a)
       => T vs1 a rel
       -> T vs2 a rel
       -> RuleF rel ts
            ('St n steps c)
            ('St n (Snoc steps ('PremStep ('Goal "=/=" (Union vs1 vs2) '[]))) c)
            ()

  -- | Lift an immediate rel action (executed during interpretation)
  LiftRelF :: rel a
           -> RuleF rel ts s s a

  -- | Lift a deferred rel action (executed after premises)
  LiftRelDeferredF :: rel ()
                   -> RuleF rel ts s s ()
