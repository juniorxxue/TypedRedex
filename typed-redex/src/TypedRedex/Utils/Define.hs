{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

-- | Clean DSL syntax for defining relations using inference-rule style.
--
-- This module provides a cleaner alternative to the callback-based rule syntax.
-- Instead of:
--
-- @
-- natLt = rules2 "natLt" [natLtZero, natLtSucc]
--   where
--     natLtZero = rule2 "natLt-Zero" $ \\natLt' ->
--       fresh $ \\m' -> natLt' zro (suc m')
-- @
--
-- You can write:
--
-- @
-- natLt = define2 "natLt"
--   [ fresh $ \\m' ->
--       concl $ natLt zro (suc m')
--   , fresh2 $ \\n' m' -> do
--       concl $ natLt (suc n') (suc m')
--       prem  $ natLt n' m'
--   ]
--   where concl = concl2; prem = prem2
-- @
--
-- The key insight: relations return 'Applied2' which stores both arguments
-- and goal. 'concl2' extracts the arguments and unifies with implicit rule args.

module TypedRedex.Utils.Define
  ( -- * Applied relation types (store args + goal)
    Applied(..)
  , Applied2(..)
  , Applied3(..)
  , Applied4(..)
  , Applied5(..)
    -- * Conclusion (extract pattern, unify with rule args)
  , concl1, concl2, concl3, concl4, concl5
    -- * Premise (run the goal) - overloaded via type class
  , Premise(..)
    -- * Define combinators
  , define, define2, define3, define4, define5
  ) where

import TypedRedex.Core.Internal.Redex
import TypedRedex.Core.Internal.Logic
import TypedRedex.Utils.Redex
import Control.Applicative (asum)

--------------------------------------------------------------------------------
-- Applied types: store arguments + goal
--------------------------------------------------------------------------------

-- | Applied unary relation: stores argument and goal.
data Applied rel a = Applied
  { app1Arg  :: L a rel
  , app1Goal :: rel ()
  }

-- | Applied binary relation: stores arguments and goal.
data Applied2 rel a b = Applied2
  { app2Args :: (L a rel, L b rel)
  , app2Goal :: rel ()
  }

-- | Applied ternary relation: stores arguments and goal.
data Applied3 rel a b c = Applied3
  { app3Args :: (L a rel, L b rel, L c rel)
  , app3Goal :: rel ()
  }

-- | Applied quaternary relation: stores arguments and goal.
data Applied4 rel a b c d = Applied4
  { app4Args :: (L a rel, L b rel, L c rel, L d rel)
  , app4Goal :: rel ()
  }

-- | Applied 5-ary relation: stores arguments and goal.
data Applied5 rel a b c d e = Applied5
  { app5Args :: (L a rel, L b rel, L c rel, L d rel, L e rel)
  , app5Goal :: rel ()
  }

--------------------------------------------------------------------------------
-- Conclusion: extract pattern args and unify with rule args
--------------------------------------------------------------------------------

-- | Conclusion for unary relations.
concl1 :: (Redex rel, LogicType a, ?conclArg :: L a rel)
       => Applied rel a -> rel ()
concl1 (Applied px _) = ?conclArg <=> px

-- | Conclusion for binary relations.
--
-- @
-- concl2 $ natLt zro (suc m')
-- @
concl2 :: (Redex rel, LogicType a, LogicType b, ?conclArgs :: (L a rel, L b rel))
       => Applied2 rel a b -> rel ()
concl2 (Applied2 (px, py) _) =
  let (x, y) = ?conclArgs
  in x <=> px >> y <=> py

-- | Conclusion for ternary relations.
concl3 :: (Redex rel, LogicType a, LogicType b, LogicType c, ?conclArgs :: (L a rel, L b rel, L c rel))
       => Applied3 rel a b c -> rel ()
concl3 (Applied3 (px, py, pz) _) =
  let (x, y, z) = ?conclArgs
  in x <=> px >> y <=> py >> z <=> pz

-- | Conclusion for quaternary relations.
concl4 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d, ?conclArgs :: (L a rel, L b rel, L c rel, L d rel))
       => Applied4 rel a b c d -> rel ()
concl4 (Applied4 (px, py, pz, pw) _) =
  let (x, y, z, w) = ?conclArgs
  in x <=> px >> y <=> py >> z <=> pz >> w <=> pw

-- | Conclusion for 5-ary relations.
concl5 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d, LogicType e, ?conclArgs :: (L a rel, L b rel, L c rel, L d rel, L e rel))
       => Applied5 rel a b c d e -> rel ()
concl5 (Applied5 (px, py, pz, pw, pv) _) =
  let (x, y, z, w, v) = ?conclArgs
  in x <=> px >> y <=> py >> z <=> pz >> w <=> pw >> v <=> pv

--------------------------------------------------------------------------------
-- Premise: type class for running applied relations
--------------------------------------------------------------------------------

-- | Type class for running an applied relation as a premise.
--
-- Overloaded for all arities, so you can just write @prem $ rel args...@
class Premise app rel where
  prem :: app -> rel ()

instance (Redex rel) => Premise (Applied rel a) rel where
  prem (Applied _ g) = call $ Relation "" [] g

instance (Redex rel) => Premise (Applied2 rel a b) rel where
  prem (Applied2 _ g) = call $ Relation "" [] g

instance (Redex rel) => Premise (Applied3 rel a b c) rel where
  prem (Applied3 _ g) = call $ Relation "" [] g

instance (Redex rel) => Premise (Applied4 rel a b c d) rel where
  prem (Applied4 _ g) = call $ Relation "" [] g

instance (Redex rel) => Premise (Applied5 rel a b c d e) rel where
  prem (Applied5 _ g) = call $ Relation "" [] g

--------------------------------------------------------------------------------
-- Define combinators
--------------------------------------------------------------------------------

-- | Define a unary relation from a list of rules.
--
-- The list is constructed inside the implicit param context.
define :: (Redex rel, LogicType a)
       => String
       -> ((?conclArg :: L a rel) => [rel ()])
       -> L a rel -> Applied rel a
define name rules x = Applied x $ argument x $ \x' ->
  let ?conclArg = x'
  in asum rules

-- | Define a binary relation from a list of rules.
--
-- @
-- natLt = define2 "natLt"
--   [ fresh $ \\m' ->
--       concl2 $ natLt zro (suc m')
--   , fresh2 $ \\n' m' -> do
--       concl2 $ natLt (suc n') (suc m')
--       prem2  $ natLt n' m'
--   ]
-- @
define2 :: (Redex rel, LogicType a, LogicType b)
        => String
        -> ((?conclArgs :: (L a rel, L b rel)) => [rel ()])
        -> L a rel -> L b rel -> Applied2 rel a b
define2 name rules x y = Applied2 (x, y) $ argument2 x y $ \x' y' ->
  let ?conclArgs = (x', y')
  in asum rules

-- | Define a ternary relation from a list of rules.
define3 :: (Redex rel, LogicType a, LogicType b, LogicType c)
        => String
        -> ((?conclArgs :: (L a rel, L b rel, L c rel)) => [rel ()])
        -> L a rel -> L b rel -> L c rel -> Applied3 rel a b c
define3 name rules x y z = Applied3 (x, y, z) $ argument3 x y z $ \x' y' z' ->
  let ?conclArgs = (x', y', z')
  in asum rules

-- | Define a quaternary relation from a list of rules.
define4 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d)
        => String
        -> ((?conclArgs :: (L a rel, L b rel, L c rel, L d rel)) => [rel ()])
        -> L a rel -> L b rel -> L c rel -> L d rel -> Applied4 rel a b c d
define4 name rules x y z w = Applied4 (x, y, z, w) $ argument4 x y z w $ \x' y' z' w' ->
  let ?conclArgs = (x', y', z', w')
  in asum rules

-- | Define a 5-ary relation from a list of rules.
define5 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d, LogicType e)
        => String
        -> ((?conclArgs :: (L a rel, L b rel, L c rel, L d rel, L e rel)) => [rel ()])
        -> L a rel -> L b rel -> L c rel -> L d rel -> L e rel -> Applied5 rel a b c d e
define5 name rules x y z w v = Applied5 (x, y, z, w, v) $ argument5 x y z w v $ \x' y' z' w' v' ->
  let ?conclArgs = (x', y', z', w', v')
  in asum rules
