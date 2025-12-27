{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}

-- | Indexed Free Monad
--
-- This module provides an indexed (graded) free monad that tracks
-- state transitions at the type level. This enables compile-time
-- verification of stateful computations.
--
-- = Key Types
--
-- @
-- IxFree f i j a
--   f : indexed functor (operations with state transitions)
--   i : input state (state before computation)
--   j : output state (state after computation)
--   a : result type
-- @
--
-- = State Threading
--
-- The indexed bind chains state transitions:
--
-- @
-- (>>=) :: IxFree f i j a -> (a -> IxFree f j k b) -> IxFree f i k b
--                  ^                   ^
--                  └───── must match ──┘
-- @
--
-- = Usage with QualifiedDo
--
-- @
-- {-# LANGUAGE QualifiedDo #-}
-- import qualified TypedRedex.Free.IxFree as Ix
--
-- example :: IxFree F ('St 0) ('St 2) ()
-- example = Ix.do
--   x <- op1      -- 'St 0 -> 'St 1
--   y <- op2 x    -- 'St 1 -> 'St 2
--   Ix.return ()
-- @
module TypedRedex.Free.IxFree
  ( -- * Indexed Free Monad
    IxFree(..)
    -- * Operations
  , liftF
  , foldIxFree
    -- * QualifiedDo Support
  , return
  , (>>=)
  , (>>)
  ) where

import Prelude hiding (return, (>>=), (>>))
import Data.Kind (Type)

-- | Indexed Free Monad
--
-- A free monad over an indexed functor @f@, where:
--
-- * @i@ is the input state (before running the computation)
-- * @j@ is the output state (after running the computation)
-- * @a@ is the result type
--
-- The structure is:
--
-- * 'Pure' represents a completed computation that doesn't change state
-- * 'Bind' represents an operation followed by a continuation
data IxFree (f :: k -> k -> Type -> Type) (i :: k) (j :: k) (a :: Type) where
  -- | A pure value (identity state transition: i -> i)
  Pure :: a -> IxFree f i i a

  -- | An operation followed by a continuation
  -- The operation goes from state i to state m
  -- The continuation goes from state m to state j
  Bind :: f i m x -> (x -> IxFree f m j a) -> IxFree f i j a

-- | Lift a single operation into 'IxFree'
liftF :: f i j a -> IxFree f i j a
liftF op = Bind op Pure

-- | Fold (interpret) an 'IxFree' using natural transformations
--
-- @
-- foldIxFree eta phi free
--   eta : embed pure values
--   phi : interpret operations (must be polymorphic in input state)
-- @
foldIxFree :: forall f g i j a.
              (forall x k. x -> g k k x)                           -- ^ Pure handler
           -> (forall i' x m k. f i' m x -> (x -> g m k a) -> g i' k a)  -- ^ Operation handler
           -> IxFree f i j a
           -> g i j a
foldIxFree eta _   (Pure a)     = eta a
foldIxFree eta phi (Bind op k)  = phi op (\x -> foldIxFree eta phi (k x))

--------------------------------------------------------------------------------
-- QualifiedDo Support
--------------------------------------------------------------------------------

-- | Return (pure) for indexed monad
return :: a -> IxFree f i i a
return = Pure

-- | Bind for indexed monad
--
-- Note: The intermediate state @j@ must match between the left computation's
-- output and the right computation's input.
(>>=) :: IxFree f i j a -> (a -> IxFree f j k b) -> IxFree f i k b
Pure a   >>= f = f a
Bind op k >>= f = Bind op (\x -> k x >>= f)

-- | Sequence for indexed monad
(>>) :: IxFree f i j a -> IxFree f j k b -> IxFree f i k b
m >> n = m >>= \_ -> n

infixl 1 >>=, >>
