{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

-- | Fresh variable allocation utilities.
--
-- This module provides combinators for allocating fresh logic variables
-- and binding arguments to local variables.
--
-- The 'Freshable' class unifies fresh allocation for both logic variables
-- and nominal atoms, allowing mixed usage in 'fresh2', 'fresh3', etc.
module TypedRedex.DSL.Fresh
  ( -- * Type aliases
    LVar, LTerm
    -- * Freshable class
  , Freshable(..)
    -- * Fresh variable allocation
  , fresh, fresh2, fresh3, fresh4, fresh5, fresh6, fresh7
    -- * Logic-only fresh (for backward compatibility)
  , freshLogic
    -- * Argument binding
  , argument, argument2, argument3, argument4, argument5
  ) where

import TypedRedex.Core.Internal.Redex
import TypedRedex.Core.Internal.Logic

-- | A logic variable in a relation.
type LVar a rel = Var a (RVar rel)

-- | A logic term in a relation.
type LTerm a rel = Logic a (RVar rel)

--------------------------------------------------------------------------------
-- Freshable class
--------------------------------------------------------------------------------

-- | Class for types that can be freshly allocated in a relation.
--
-- This unifies logic variables ('LTerm') and nominal atoms ('Nom', 'TyNom').
-- The type of each variable in 'fresh2', 'fresh3', etc. is inferred from usage.
--
-- @
-- fresh3 $ \\ctx x body -> do
--   -- ctx :: LTerm Ctx rel  (inferred from typeof ctx ...)
--   -- x :: Nom              (inferred from bind x body)
--   -- body :: LTerm Tm rel  (inferred from lam ... body)
-- @
class Freshable a rel where
  freshOne :: (a -> rel s) -> rel s

-- | Instance for logic variables.
instance (Redex rel, LogicType t) => Freshable (LTerm t rel) rel where
  freshOne f = fresh_ FreshVar $ f . Free

--------------------------------------------------------------------------------
-- Fresh variable allocation
--------------------------------------------------------------------------------

-- | Allocate a fresh variable (logic variable or nominal atom).
fresh :: Freshable a rel => (a -> rel s) -> rel s
fresh = freshOne

-- | Allocate a fresh logic variable (explicit, for backward compatibility).
freshLogic :: (Redex rel, LogicType a) => (LTerm a rel -> rel s) -> rel s
freshLogic f = fresh_ FreshVar $ f . Free

-- | Allocate two fresh variables.
fresh2 :: (Freshable a rel, Freshable b rel)
       => (a -> b -> rel s) -> rel s
fresh2 f = freshOne $ \a -> freshOne $ \b -> f a b

-- | Allocate three fresh variables.
fresh3 :: (Freshable a rel, Freshable b rel, Freshable c rel)
       => (a -> b -> c -> rel s) -> rel s
fresh3 f = freshOne $ \a -> freshOne $ \b -> freshOne $ \c -> f a b c

-- | Allocate four fresh variables.
fresh4 :: (Freshable a rel, Freshable b rel, Freshable c rel, Freshable d rel)
       => (a -> b -> c -> d -> rel s) -> rel s
fresh4 f = freshOne $ \a -> freshOne $ \b -> freshOne $ \c -> freshOne $ \d -> f a b c d

-- | Allocate five fresh variables.
fresh5 :: (Freshable a rel, Freshable b rel, Freshable c rel, Freshable d rel, Freshable e rel)
       => (a -> b -> c -> d -> e -> rel s) -> rel s
fresh5 f = freshOne $ \a -> freshOne $ \b -> freshOne $ \c -> freshOne $ \d -> freshOne $ \e -> f a b c d e

-- | Allocate six fresh variables.
fresh6 :: (Freshable a rel, Freshable b rel, Freshable c rel, Freshable d rel, Freshable e rel, Freshable f' rel)
       => (a -> b -> c -> d -> e -> f' -> rel s) -> rel s
fresh6 f = freshOne $ \a -> freshOne $ \b -> freshOne $ \c -> freshOne $ \d -> freshOne $ \e -> freshOne $ \f' -> f a b c d e f'

-- | Allocate seven fresh variables.
fresh7 :: (Freshable a rel, Freshable b rel, Freshable c rel, Freshable d rel, Freshable e rel, Freshable f' rel, Freshable g rel)
       => (a -> b -> c -> d -> e -> f' -> g -> rel s) -> rel s
fresh7 f = freshOne $ \a -> freshOne $ \b -> freshOne $ \c -> freshOne $ \d -> freshOne $ \e -> freshOne $ \f' -> freshOne $ \g -> f a b c d e f' g

--------------------------------------------------------------------------------
-- Argument binding
--------------------------------------------------------------------------------

-- | Bind an argument to a fresh local variable.
argument :: (Redex rel, LogicType a) => LTerm a rel -> (LTerm a rel -> rel s) -> rel s
argument x f = fresh_ (ArgVar x) $ f . Free

-- | Bind two arguments to fresh local variables.
argument2 :: (Redex rel, LogicType a, LogicType b) => LTerm a rel -> LTerm b rel -> (LTerm a rel -> LTerm b rel -> rel s) -> rel s
argument2 a_ b_ f = argument a_ $ \a -> argument b_ $ \b -> f a b

-- | Bind three arguments to fresh local variables.
argument3 :: (Redex rel, LogicType a, LogicType b, LogicType c) => LTerm a rel -> LTerm b rel -> LTerm c rel -> (LTerm a rel -> LTerm b rel -> LTerm c rel -> rel s) -> rel s
argument3 a_ b_ c_ f = argument a_ $ \a -> argument b_ $ \b -> argument c_ $ \c -> f a b c

-- | Bind four arguments to fresh local variables.
argument4 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d) => LTerm a rel -> LTerm b rel -> LTerm c rel -> LTerm d rel -> (LTerm a rel -> LTerm b rel -> LTerm c rel -> LTerm d rel -> rel s) -> rel s
argument4 a_ b_ c_ d_ f = argument a_ $ \a -> argument b_ $ \b -> argument c_ $ \c -> argument d_ $ \d -> f a b c d

-- | Bind five arguments to fresh local variables.
argument5 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d, LogicType e) => LTerm a rel -> LTerm b rel -> LTerm c rel -> LTerm d rel -> LTerm e rel -> (LTerm a rel -> LTerm b rel -> LTerm c rel -> LTerm d rel -> LTerm e rel -> rel s) -> rel s
argument5 a_ b_ c_ d_ e_ f = argument a_ $ \a -> argument b_ $ \b -> argument c_ $ \c -> argument d_ $ \d -> argument e_ $ \e -> f a b c d e
