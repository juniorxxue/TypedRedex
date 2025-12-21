-- | Relation construction and invocation utilities.
--
-- This module provides solver primitives for constructing named relations
-- and invoking them with different suspension behaviors.
--
-- This is part of Core/Internal because these are low-level solver primitives.
module TypedRedex.Core.Internal.Relation
  ( -- * Relation construction
    relation, relation2, relation3, relation4, relation5
    -- * Relation invocation
  , call, callDirect
    -- * Unification operators
  , (<=>)
    -- * Disjunction
  , conde
  ) where

import TypedRedex.Core.Internal.Redex
import TypedRedex.Core.Internal.Logic
import TypedRedex.DSL.Fresh
import Control.Applicative (asum)

--------------------------------------------------------------------------------
-- Relation construction
--------------------------------------------------------------------------------

-- | Define a unary relation.
relation :: (Redex rel, LogicType a) => String -> (LTerm a rel -> Goal rel) -> LTerm a rel -> Relation rel
relation n f a_ = Relation n [CapturedTerm a_] $ argument a_ f

-- | Define a binary relation.
relation2 :: (Redex rel, LogicType a, LogicType b) => String -> (LTerm a rel -> LTerm b rel -> Goal rel) -> LTerm a rel -> LTerm b rel -> Relation rel
relation2 n f a_ b_ = Relation n [CapturedTerm a_, CapturedTerm b_] $ argument2 a_ b_ f

-- | Define a ternary relation.
relation3 :: (Redex rel, LogicType a, LogicType b, LogicType c) => String -> (LTerm a rel -> LTerm b rel -> LTerm c rel -> Goal rel) -> LTerm a rel -> LTerm b rel -> LTerm c rel -> Relation rel
relation3 n f a_ b_ c_ = Relation n [CapturedTerm a_, CapturedTerm b_, CapturedTerm c_] $ argument3 a_ b_ c_ f

-- | Define a quaternary relation.
relation4 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d) => String -> (LTerm a rel -> LTerm b rel -> LTerm c rel -> LTerm d rel -> Goal rel) -> LTerm a rel -> LTerm b rel -> LTerm c rel -> LTerm d rel -> Relation rel
relation4 n f a_ b_ c_ d_ = Relation n [CapturedTerm a_, CapturedTerm b_, CapturedTerm c_, CapturedTerm d_] $ argument4 a_ b_ c_ d_ f

-- | Define a 5-ary relation.
relation5 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d, LogicType e) => String -> (LTerm a rel -> LTerm b rel -> LTerm c rel -> LTerm d rel -> LTerm e rel -> Goal rel) -> LTerm a rel -> LTerm b rel -> LTerm c rel -> LTerm d rel -> LTerm e rel -> Relation rel
relation5 n f a_ b_ c_ d_ e_ = Relation n [CapturedTerm a_, CapturedTerm b_, CapturedTerm c_, CapturedTerm d_, CapturedTerm e_] $ argument5 a_ b_ c_ d_ e_ f

--------------------------------------------------------------------------------
-- Relation invocation
--------------------------------------------------------------------------------

-- | Invoke a relation with suspension (for fair interleaving).
--
-- This is the standard way to call a relation. The suspension ensures
-- fair interleaving in the search, preventing one branch from starving others.
call :: (Redex rel) => Relation rel -> Goal rel
call = call_ Opaque

-- | Invoke a relation without suspension (direct/transparent execution).
--
-- Use this when you want to inline a relation call without fair interleaving.
-- This is useful for helper relations that should execute immediately.
--
-- @
-- run f = fresh $ \\x -> do
--   callDirect $ f x  -- Execute without suspension
--   eval x
-- @
callDirect :: (Redex rel) => Relation rel -> Goal rel
callDirect = call_ Transparent

--------------------------------------------------------------------------------
-- Unification operators
--------------------------------------------------------------------------------

-- | Unify two logic terms.
--
-- This is the primary unification operator. Use it for equating logic terms:
--
-- @
-- fresh2 $ \\x y -> do
--   x <=> y           -- Unify two logic variables
--   x <=> Ground (project someValue)  -- Unify with a ground value
-- @
(<=>) :: (LogicType a, Redex rel) => LTerm a rel -> LTerm a rel -> Goal rel
a <=> b = unify a b

--------------------------------------------------------------------------------
-- Disjunction
--------------------------------------------------------------------------------

-- | Try multiple alternatives (disjunction).
conde :: (Redex rel) => [Goal rel] -> Goal rel
conde = asum
