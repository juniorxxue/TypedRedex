{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Shallow.Core.Internal.Kanren where

import Data.Kind (Type)
import Control.Applicative (Alternative(empty, (<|>)))
import Unbound.Generics.LocallyNameless (Fresh)
import Shallow.Core.Internal.Logic

data Relation (rel :: Type -> Type) = Relation String (rel ())

data FreshType (rel :: Type -> Type) (t :: Type) where
    FreshVar :: FreshType rel t
    ArgVar :: (Kanren rel, LogicType t) => Logic t (KVar rel) -> FreshType rel t

data CallType = Opaque | Transparent

-- ============================================================================
-- KANREN with Fresh
-- ============================================================================
-- Key change: Added Fresh constraint
-- Now the rel monad must support Fresh operations

class (Alternative rel, Fresh rel, Functor (KVar rel)) => Kanren rel where

    data KVar rel :: Type -> Type

    fresh_ :: (LogicType t) => FreshType rel t -> (KVar rel (Logic t (KVar rel)) -> rel a) -> rel a

    unify :: (LogicType a) => Logic a (KVar rel) -> Logic a (KVar rel) -> rel ()

    call_ :: CallType -> Relation rel -> rel ()

    displayVar :: KVar rel t -> String

class (Kanren rel) => KanrenEval rel where

    derefVar :: (LogicType a) => KVar rel (Logic a (KVar rel)) -> rel a

class EqVar rel where

    varEq :: (KVar rel) a -> (KVar rel) b -> Bool
