{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Shallow.Core.Internal.Logic where

import Data.Kind (Type)
import Data.Proxy (Proxy)
import Control.Applicative
import Unbound.Generics.LocallyNameless (Fresh)

data Field a var where
  Field :: LogicType x => Proxy x -> Logic x var -> Field a var

data Constructor a var = Constructor
  { name :: String
  , construct :: [Field a var] -> Reified a var
  }

-- Keep var as a type constructor (Type -> Type), same as original design
type Var x (var :: Type -> Type) = var (Logic x var)

data Logic a (var :: Type -> Type)
  = Free (Var a var)
  | Ground (Reified a var)

-- ============================================================================
-- MONADIC LogicType
-- ============================================================================
-- Key change: project and reify are now MONADIC
-- This allows them to use Fresh operations from unbound-generics

class LogicType a where
  data Reified a (var :: Type -> Type) :: Type

  -- MONADIC projection (was pure before)
  -- Now can use: unbind, fresh, aeq, etc.
  project :: (Monad m, Fresh m) => a -> m (Reified a var)

  -- MONADIC reification (was pure before)
  reify :: (Monad m, Fresh m) => Reified a var -> m (Maybe a)

  -- Unification: now the rel monad can also support Fresh
  unifyVal :: (Alternative rel, Fresh rel) =>
    (forall t. LogicType t => Logic t var -> Logic t var -> rel ())
    -> Reified a var -> Reified a var -> rel ()

  -- Quote for pretty printing (keep pure)
  quote :: Reified a var -> (String, [Field a var])

  -- Dereference (monadic)
  derefVal :: (Alternative m, Monad m, Fresh m) =>
    (forall t. LogicType t => Logic t var -> m t)
    -> Reified a var -> m a
