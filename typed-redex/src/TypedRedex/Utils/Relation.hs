-- | Relation construction and invocation utilities.
--
-- This module provides combinators for constructing named relations
-- and invoking them with different suspension behaviors.
module TypedRedex.Utils.Relation
  ( -- * Relation construction
    relation, relation2, relation3, relation4, relation5
    -- * Relation invocation
  , call, premise, embed
    -- * Unification operators
  , (===), (<=>)
    -- * Disjunction
  , conde
  ) where

import TypedRedex.Core.Internal.Redex
import TypedRedex.Core.Internal.Logic
import TypedRedex.Utils.Fresh
import Control.Applicative (asum)

--------------------------------------------------------------------------------
-- Relation construction
--------------------------------------------------------------------------------

-- | Define a unary relation.
relation :: (Redex rel, LogicType a) => String -> (L a rel -> rel ()) -> L a rel -> Relation rel
relation n f a_ = Relation n [CapturedTerm a_] $ argument a_ f

-- | Define a binary relation.
relation2 :: (Redex rel, LogicType a, LogicType b) => String -> (L a rel -> L b rel -> rel ()) -> L a rel -> L b rel -> Relation rel
relation2 n f a_ b_ = Relation n [CapturedTerm a_, CapturedTerm b_] $ argument2 a_ b_ f

-- | Define a ternary relation.
relation3 :: (Redex rel, LogicType a, LogicType b, LogicType c) => String -> (L a rel -> L b rel -> L c rel -> rel ()) -> L a rel -> L b rel -> L c rel -> Relation rel
relation3 n f a_ b_ c_ = Relation n [CapturedTerm a_, CapturedTerm b_, CapturedTerm c_] $ argument3 a_ b_ c_ f

-- | Define a quaternary relation.
relation4 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d) => String -> (L a rel -> L b rel -> L c rel -> L d rel -> rel ()) -> L a rel -> L b rel -> L c rel -> L d rel -> Relation rel
relation4 n f a_ b_ c_ d_ = Relation n [CapturedTerm a_, CapturedTerm b_, CapturedTerm c_, CapturedTerm d_] $ argument4 a_ b_ c_ d_ f

-- | Define a 5-ary relation.
relation5 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d, LogicType e) => String -> (L a rel -> L b rel -> L c rel -> L d rel -> L e rel -> rel ()) -> L a rel -> L b rel -> L c rel -> L d rel -> L e rel -> Relation rel
relation5 n f a_ b_ c_ d_ e_ = Relation n [CapturedTerm a_, CapturedTerm b_, CapturedTerm c_, CapturedTerm d_, CapturedTerm e_] $ argument5 a_ b_ c_ d_ e_ f

--------------------------------------------------------------------------------
-- Relation invocation
--------------------------------------------------------------------------------

-- | Invoke a relation with suspension (for fair interleaving).
call :: (Redex rel) => Relation rel -> rel ()
call = call_ Opaque

-- | Alias for 'call'. Use in inference rules to invoke premises.
premise :: (Redex rel) => Relation rel -> rel ()
premise = call

-- | Invoke a relation without suspension (transparent embedding).
embed :: (Redex rel) => Relation rel -> rel ()
embed = call_ Transparent

--------------------------------------------------------------------------------
-- Unification operators
--------------------------------------------------------------------------------

-- | Unify a logic term with a ground pattern.
(===) :: (LogicType a, Redex rel) => L a rel -> Reified a (RVar rel) -> rel ()
a === b = unify a (Ground b)

-- | Unify two logic terms.
(<=>) :: (LogicType a, Redex rel) => L a rel -> L a rel -> rel ()
a <=> b = unify a b

--------------------------------------------------------------------------------
-- Disjunction
--------------------------------------------------------------------------------

-- | Try multiple alternatives (disjunction).
conde :: (Redex rel) => [rel a] -> rel a
conde = asum
