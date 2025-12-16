{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

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
-- @
--
-- Both 'concl' and 'prem' are overloaded and work for any arity.

module TypedRedex.Utils.Define
  ( -- * Applied relation types (store args + goal)
    Applied(..)
  , Applied2(..)
  , Applied3(..)
  , Applied4(..)
  , Applied5(..)
    -- * Conclusion and Premise (overloaded)
  , Conclude(..)
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
-- Conclude: type class with type family for pattern type
--------------------------------------------------------------------------------

-- | Type class for extracting conclusion pattern and unifying.
--
-- The key trick: 'ConcludePat' is a type family that computes the pattern type,
-- and the implicit param @?concl@ uses this computed type. This avoids putting
-- implicit params in instance contexts (which GHC forbids).
class Conclude app rel where
  -- | The type of the pattern (arguments) stored in this applied relation.
  type ConcludePat app

  -- | Extract pattern and unify with rule arguments via implicit @?concl@.
  concl :: (?concl :: ConcludePat app -> rel ()) => app -> rel ()

instance Conclude (Applied rel a) rel where
  type ConcludePat (Applied rel a) = L a rel
  concl (Applied px _) = ?concl px

instance Conclude (Applied2 rel a b) rel where
  type ConcludePat (Applied2 rel a b) = (L a rel, L b rel)
  concl (Applied2 pat _) = ?concl pat

instance Conclude (Applied3 rel a b c) rel where
  type ConcludePat (Applied3 rel a b c) = (L a rel, L b rel, L c rel)
  concl (Applied3 pat _) = ?concl pat

instance Conclude (Applied4 rel a b c d) rel where
  type ConcludePat (Applied4 rel a b c d) = (L a rel, L b rel, L c rel, L d rel)
  concl (Applied4 pat _) = ?concl pat

instance Conclude (Applied5 rel a b c d e) rel where
  type ConcludePat (Applied5 rel a b c d e) = (L a rel, L b rel, L c rel, L d rel, L e rel)
  concl (Applied5 pat _) = ?concl pat

--------------------------------------------------------------------------------
-- Premise: type class for running applied relations
--------------------------------------------------------------------------------

-- | Type class for running an applied relation as a premise.
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
define :: (Redex rel, LogicType a)
       => String
       -> ((?concl :: L a rel -> rel ()) => [rel ()])
       -> L a rel -> Applied rel a
define name rules x = Applied x $ argument x $ \x' ->
  let ?concl = \px -> x' <=> px
  in asum rules

-- | Define a binary relation from a list of rules.
--
-- @
-- natLt = define2 "natLt"
--   [ fresh $ \\m' ->
--       concl $ natLt zro (suc m')
--   , fresh2 $ \\n' m' -> do
--       concl $ natLt (suc n') (suc m')
--       prem  $ natLt n' m'
--   ]
-- @
define2 :: (Redex rel, LogicType a, LogicType b)
        => String
        -> ((?concl :: (L a rel, L b rel) -> rel ()) => [rel ()])
        -> L a rel -> L b rel -> Applied2 rel a b
define2 name rules x y = Applied2 (x, y) $ argument2 x y $ \x' y' ->
  let ?concl = \(px, py) -> x' <=> px >> y' <=> py
  in asum rules

-- | Define a ternary relation from a list of rules.
define3 :: (Redex rel, LogicType a, LogicType b, LogicType c)
        => String
        -> ((?concl :: (L a rel, L b rel, L c rel) -> rel ()) => [rel ()])
        -> L a rel -> L b rel -> L c rel -> Applied3 rel a b c
define3 name rules x y z = Applied3 (x, y, z) $ argument3 x y z $ \x' y' z' ->
  let ?concl = \(px, py, pz) -> x' <=> px >> y' <=> py >> z' <=> pz
  in asum rules

-- | Define a quaternary relation from a list of rules.
define4 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d)
        => String
        -> ((?concl :: (L a rel, L b rel, L c rel, L d rel) -> rel ()) => [rel ()])
        -> L a rel -> L b rel -> L c rel -> L d rel -> Applied4 rel a b c d
define4 name rules x y z w = Applied4 (x, y, z, w) $ argument4 x y z w $ \x' y' z' w' ->
  let ?concl = \(px, py, pz, pw) -> x' <=> px >> y' <=> py >> z' <=> pz >> w' <=> pw
  in asum rules

-- | Define a 5-ary relation from a list of rules.
define5 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d, LogicType e)
        => String
        -> ((?concl :: (L a rel, L b rel, L c rel, L d rel, L e rel) -> rel ()) => [rel ()])
        -> L a rel -> L b rel -> L c rel -> L d rel -> L e rel -> Applied5 rel a b c d e
define5 name rules x y z w v = Applied5 (x, y, z, w, v) $ argument5 x y z w v $ \x' y' z' w' v' ->
  let ?concl = \(px, py, pz, pw, pv) -> x' <=> px >> y' <=> py >> z' <=> pz >> w' <=> pw >> v' <=> pv
  in asum rules
