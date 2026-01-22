-- | Indexed Free Monad
--
-- Tracks state transitions at the type level for compile-time verification.
module TypedRedex.Core.IxFree
  ( IxFree(..)
  , liftF
  , foldIxFree
  -- * QualifiedDo
  , return, (>>=), (>>)
  ) where

import Prelude hiding (return, (>>=), (>>))
import Data.Kind (Type)

-- | Indexed free monad over functor @f@ with states @i@ → @j@
data IxFree (f :: k -> k -> Type -> Type) (i :: k) (j :: k) (a :: Type) where
  Pure :: a -> IxFree f i i a
  Bind :: f i m x -> (x -> IxFree f m j a) -> IxFree f i j a

liftF :: f i j a -> IxFree f i j a
liftF op = Bind op Pure

foldIxFree
  :: (forall x s. x -> g s s x)
  -> (forall s m x t. f s m x -> (x -> g m t a) -> g s t a)
  -> IxFree f i j a -> g i j a
foldIxFree eta _   (Pure a)    = eta a
foldIxFree eta phi (Bind op k) = phi op (foldIxFree eta phi . k)

-- QualifiedDo support
return :: a -> IxFree f i i a
return = Pure

(>>=) :: IxFree f i j a -> (a -> IxFree f j k b) -> IxFree f i k b
Pure a    >>= f = f a
Bind op k >>= f = Bind op (\x -> k x >>= f)

(>>) :: IxFree f i j a -> IxFree f j k b -> IxFree f i k b
m >> n = m >>= \_ -> n

infixl 1 >>=, >>
