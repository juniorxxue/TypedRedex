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
--
-- @
-- lookupTm = judgment3 "lookupTm" [lookupTmHere, lookupTmThere, lookupTmSkip]
--   where
--     lookupTmHere = rule "lookup-here" $ fresh2 $ \\ty rest ->
--       concl $ lookupTm (tmBind ty rest) zro ty
--
--     lookupTmThere = rule "lookup-there" $ fresh4 $ \\ty ty' rest n' -> do
--       concl $ lookupTm (tmBind ty' rest) (suc n') ty
--       prem  $ lookupTm rest n' ty
-- @
--
-- Both 'concl' and 'prem' are overloaded and work for any arity.
-- Rule names are tracked for derivation trees.

module TypedRedex.DSL.Define
  ( -- * Applied relation types (store args + goal)
    Applied(..)
  , Applied2(..)
  , Applied3(..)
  , Applied4(..)
  , Applied5(..)
    -- * Conclusion and Premise (overloaded)
  , Conclude(..)
  , Premise(..)
    -- * Named rules
  , Rule(..), Rule2(..), Rule3(..), Rule4(..), Rule5(..)
  , rule, rule1, rule2, rule3, rule4, rule5
    -- * Judgment combinators (combine named rules)
  , judgment, judgment2, judgment3, judgment4, judgment5
  ) where

import TypedRedex.Core.Internal.Redex
import TypedRedex.Core.Internal.Logic
import TypedRedex.DSL.Fresh (L, argument, argument2, argument3, argument4, argument5)
import TypedRedex.Core.Internal.Relation (call, (<=>))
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
class Conclude app rel where
  type ConcludePat app
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
  prem (Applied _ g) = g

instance (Redex rel) => Premise (Applied2 rel a b) rel where
  prem (Applied2 _ g) = g

instance (Redex rel) => Premise (Applied3 rel a b c) rel where
  prem (Applied3 _ g) = g

instance (Redex rel) => Premise (Applied4 rel a b c d) rel where
  prem (Applied4 _ g) = g

instance (Redex rel) => Premise (Applied5 rel a b c d e) rel where
  prem (Applied5 _ g) = g

--------------------------------------------------------------------------------
-- Named rules
--------------------------------------------------------------------------------

-- | A named rule for a unary judgment.
data Rule rel a = Rule
  { rule1Name :: String
  , rule1Body :: (?concl :: L a rel -> rel ()) => rel ()
  }

-- | A named rule for a binary judgment.
data Rule2 rel a b = Rule2
  { rule2Name :: String
  , rule2Body :: (?concl :: (L a rel, L b rel) -> rel ()) => rel ()
  }

-- | A named rule for a ternary judgment.
data Rule3 rel a b c = Rule3
  { rule3Name :: String
  , rule3Body :: (?concl :: (L a rel, L b rel, L c rel) -> rel ()) => rel ()
  }

-- | A named rule for a quaternary judgment.
data Rule4 rel a b c d = Rule4
  { rule4Name :: String
  , rule4Body :: (?concl :: (L a rel, L b rel, L c rel, L d rel) -> rel ()) => rel ()
  }

-- | A named rule for a 5-ary judgment.
data Rule5 rel a b c d e = Rule5
  { rule5Name :: String
  , rule5Body :: (?concl :: (L a rel, L b rel, L c rel, L d rel, L e rel) -> rel ()) => rel ()
  }

-- | Create a named rule. The name appears in derivation trees.
--
-- @
-- lookupHere = rule "lookup-here" $ fresh2 $ \\ty rest ->
--   concl $ lookup (cons ty rest) zro ty
-- @
class MkRule r where
  rule :: String -> r -> r

instance MkRule (Rule rel a) where
  rule name body = body { rule1Name = name }

instance MkRule (Rule2 rel a b) where
  rule name body = body { rule2Name = name }

instance MkRule (Rule3 rel a b c) where
  rule name body = body { rule3Name = name }

instance MkRule (Rule4 rel a b c d) where
  rule name body = body { rule4Name = name }

instance MkRule (Rule5 rel a b c d e) where
  rule name body = body { rule5Name = name }

-- | Smart constructor for unary rules.
rule1 :: String -> ((?concl :: L a rel -> rel ()) => rel ()) -> Rule rel a
rule1 name body = Rule name body

-- | Smart constructor for binary rules.
rule2 :: String -> ((?concl :: (L a rel, L b rel) -> rel ()) => rel ()) -> Rule2 rel a b
rule2 name body = Rule2 name body

-- | Smart constructor for ternary rules.
rule3 :: String -> ((?concl :: (L a rel, L b rel, L c rel) -> rel ()) => rel ()) -> Rule3 rel a b c
rule3 name body = Rule3 name body

-- | Smart constructor for quaternary rules.
rule4 :: String -> ((?concl :: (L a rel, L b rel, L c rel, L d rel) -> rel ()) => rel ()) -> Rule4 rel a b c d
rule4 name body = Rule4 name body

-- | Smart constructor for 5-ary rules.
rule5 :: String -> ((?concl :: (L a rel, L b rel, L c rel, L d rel, L e rel) -> rel ()) => rel ()) -> Rule5 rel a b c d e
rule5 name body = Rule5 name body

--------------------------------------------------------------------------------
-- Judgment combinators
--------------------------------------------------------------------------------

-- | Define a unary judgment from a list of named rules.
-- Note: CapturedTerm captures original terms (x, y, z) for better rule extraction.
-- For SubstRedex, these resolve after unification. For DeepRedex, ground terms print as-is.
judgment :: (Redex rel, LogicType a)
         => String
         -> [Rule rel a]
         -> L a rel -> Applied rel a
judgment _ rules x = Applied x $ argument x $ \x' ->
  let terms = [CapturedTerm x]  -- Capture original term
  in let ?concl = \px -> x' <=> px
  in asum [call $ Relation (rule1Name r) terms (rule1Body r) | r <- rules]

-- | Define a binary judgment from a list of named rules.
--
-- @
-- natLt = judgment2 "natLt" [natLtZero, natLtSucc]
--   where
--     natLtZero = rule "lt-zero" $ fresh $ \\m' ->
--       concl $ natLt zro (suc m')
--
--     natLtSucc = rule "lt-succ" $ fresh2 $ \\n' m' -> do
--       concl $ natLt (suc n') (suc m')
--       prem  $ natLt n' m'
-- @
judgment2 :: (Redex rel, LogicType a, LogicType b)
          => String
          -> [Rule2 rel a b]
          -> L a rel -> L b rel -> Applied2 rel a b
judgment2 _ rules x y = Applied2 (x, y) $ argument2 x y $ \x' y' ->
  let terms = [CapturedTerm x, CapturedTerm y]  -- Capture original terms
  in let ?concl = \(px, py) -> x' <=> px >> y' <=> py
  in asum [call $ Relation (rule2Name r) terms (rule2Body r) | r <- rules]

-- | Define a ternary judgment from a list of named rules.
judgment3 :: (Redex rel, LogicType a, LogicType b, LogicType c)
          => String
          -> [Rule3 rel a b c]
          -> L a rel -> L b rel -> L c rel -> Applied3 rel a b c
judgment3 _ rules x y z = Applied3 (x, y, z) $ argument3 x y z $ \x' y' z' ->
  let terms = [CapturedTerm x, CapturedTerm y, CapturedTerm z]  -- Capture original terms
  in let ?concl = \(px, py, pz) -> x' <=> px >> y' <=> py >> z' <=> pz
  in asum [call $ Relation (rule3Name r) terms (rule3Body r) | r <- rules]

-- | Define a quaternary judgment from a list of named rules.
judgment4 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d)
          => String
          -> [Rule4 rel a b c d]
          -> L a rel -> L b rel -> L c rel -> L d rel -> Applied4 rel a b c d
judgment4 _ rules x y z w = Applied4 (x, y, z, w) $ argument4 x y z w $ \x' y' z' w' ->
  let terms = [CapturedTerm x, CapturedTerm y, CapturedTerm z, CapturedTerm w]  -- Capture original
  in let ?concl = \(px, py, pz, pw) -> x' <=> px >> y' <=> py >> z' <=> pz >> w' <=> pw
  in asum [call $ Relation (rule4Name r) terms (rule4Body r) | r <- rules]

-- | Define a 5-ary judgment from a list of named rules.
judgment5 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d, LogicType e)
          => String
          -> [Rule5 rel a b c d e]
          -> L a rel -> L b rel -> L c rel -> L d rel -> L e rel -> Applied5 rel a b c d e
judgment5 _ rules x y z w v = Applied5 (x, y, z, w, v) $ argument5 x y z w v $ \x' y' z' w' v' ->
  let terms = [CapturedTerm x, CapturedTerm y, CapturedTerm z, CapturedTerm w, CapturedTerm v]
  in let ?concl = \(px, py, pz, pw, pv) -> x' <=> px >> y' <=> py >> z' <=> pz >> w' <=> pw >> v' <=> pv
  in asum [call $ Relation (rule5Name r) terms (rule5Body r) | r <- rules]
