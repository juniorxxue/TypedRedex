{-# LANGUAGE Rank2Types #-}

-- | Fresh variable allocation utilities.
--
-- This module provides combinators for allocating fresh logic variables
-- and binding arguments to local variables.
module TypedRedex.DSL.Fresh
  ( -- * Type aliases
    Var', L
    -- * Fresh variable allocation
  , fresh, fresh2, fresh3, fresh4, fresh5
    -- * Argument binding
  , argument, argument2, argument3, argument4, argument5
  ) where

import TypedRedex.Core.Internal.Redex
import TypedRedex.Core.Internal.Logic

-- | Shorthand for a logic variable in a relation.
type Var' a rel = Var a (RVar rel)

-- | Shorthand for a logic term in a relation.
type L a rel = Logic a (RVar rel)

--------------------------------------------------------------------------------
-- Fresh variable allocation
--------------------------------------------------------------------------------

-- | Allocate a fresh unbound logic variable.
fresh :: (Redex rel, LogicType a) => (L a rel -> rel s) -> rel s
fresh f = fresh_ FreshVar $ f . Free

-- | Allocate two fresh variables.
fresh2 :: (Redex rel, LogicType a, LogicType b) => (L a rel -> L b rel -> rel s) -> rel s
fresh2 f = fresh $ \a -> fresh $ \b -> f a b

-- | Allocate three fresh variables.
fresh3 :: (Redex rel, LogicType a, LogicType b, LogicType c) => (L a rel -> L b rel -> L c rel -> rel s) -> rel s
fresh3 f = fresh $ \a -> fresh $ \b -> fresh $ \c -> f a b c

-- | Allocate four fresh variables.
fresh4 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d) => (L a rel -> L b rel -> L c rel -> L d rel -> rel s) -> rel s
fresh4 f = fresh $ \a -> fresh $ \b -> fresh $ \c -> fresh $ \d -> f a b c d

-- | Allocate five fresh variables.
fresh5 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d, LogicType e) => (L a rel -> L b rel -> L c rel -> L d rel -> L e rel -> rel s) -> rel s
fresh5 f = fresh $ \a -> fresh $ \b -> fresh $ \c -> fresh $ \d -> fresh $ \e -> f a b c d e

--------------------------------------------------------------------------------
-- Argument binding
--------------------------------------------------------------------------------

-- | Bind an argument to a fresh local variable.
argument :: (Redex rel, LogicType a) => L a rel -> (L a rel -> rel s) -> rel s
argument x f = fresh_ (ArgVar x) $ f . Free

-- | Bind two arguments to fresh local variables.
argument2 :: (Redex rel, LogicType a, LogicType b) => L a rel -> L b rel -> (L a rel -> L b rel -> rel s) -> rel s
argument2 a_ b_ f = argument a_ $ \a -> argument b_ $ \b -> f a b

-- | Bind three arguments to fresh local variables.
argument3 :: (Redex rel, LogicType a, LogicType b, LogicType c) => L a rel -> L b rel -> L c rel -> (L a rel -> L b rel -> L c rel -> rel s) -> rel s
argument3 a_ b_ c_ f = argument a_ $ \a -> argument b_ $ \b -> argument c_ $ \c -> f a b c

-- | Bind four arguments to fresh local variables.
argument4 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d) => L a rel -> L b rel -> L c rel -> L d rel -> (L a rel -> L b rel -> L c rel -> L d rel -> rel s) -> rel s
argument4 a_ b_ c_ d_ f = argument a_ $ \a -> argument b_ $ \b -> argument c_ $ \c -> argument d_ $ \d -> f a b c d

-- | Bind five arguments to fresh local variables.
argument5 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d, LogicType e) => L a rel -> L b rel -> L c rel -> L d rel -> L e rel -> (L a rel -> L b rel -> L c rel -> L d rel -> L e rel -> rel s) -> rel s
argument5 a_ b_ c_ d_ e_ f = argument a_ $ \a -> argument b_ $ \b -> argument c_ $ \c -> argument d_ $ \d -> argument e_ $ \e -> f a b c d e
