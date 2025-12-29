-- | MiniKanren Goal AST (deeply embedded)
--
-- Placeholder: Types defined, execution not implemented.
module TypedRedex.Backend.Goal
  ( -- * Goal AST
    Goal(..)
  , VarId(..)
  -- * Substitution
  , Subst(..)
  , SomeBinding(..)
  , emptySubst
  -- * Execution (placeholder)
  , exec
  ) where

import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.Typeable (Typeable)
import TypedRedex.Core.Term (Logic, Repr)

-- | Typed variable ID
newtype VarId a = VarId Int
  deriving (Eq, Show)

-- | Goal AST (deeply embedded)
data Goal where
  Fresh    :: (Repr a, Typeable a) => (VarId a -> Goal) -> Goal
  Unify    :: (Repr a, Typeable a) => Logic a -> Logic a -> Goal
  Disunify :: (Repr a, Typeable a) => Logic a -> Logic a -> Goal
  Conj     :: Goal -> Goal -> Goal
  Disj     :: Goal -> Goal -> Goal
  Neg      :: Goal -> Goal
  Success  :: Goal
  Failure  :: Goal

-- | Existential binding
data SomeBinding where
  SomeBinding :: (Repr a, Typeable a) => Logic a -> SomeBinding

-- | Substitution: map from var IDs to bindings
data Subst = Subst
  { substBindings :: IntMap SomeBinding
  , substNextVar  :: Int
  }

emptySubst :: Subst
emptySubst = Subst IM.empty 0

-- | Execute a goal (placeholder)
exec :: Goal -> Subst -> [Subst]
exec Success s      = [s]
exec Failure _      = []
exec (Conj g1 g2) s = concatMap (exec g2) (exec g1 s)
exec (Disj g1 g2) s = interleave (exec g1 s) (exec g2 s)
exec (Fresh f) s    =
  let v = VarId (substNextVar s)
      s' = s { substNextVar = substNextVar s + 1 }
  in exec (f v) s'
exec (Unify _ _) _    = undefined  -- TODO: implement unification
exec (Disunify _ _) _ = undefined  -- TODO: implement disunification
exec (Neg _) _        = undefined  -- TODO: implement negation

interleave :: [a] -> [a] -> [a]
interleave [] ys = ys
interleave (x:xs) ys = x : interleave ys xs
