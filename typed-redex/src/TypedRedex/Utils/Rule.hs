{-# LANGUAGE Rank2Types #-}

-- | DEPRECATED: Inference-rule-style syntax for defining relations.
--
-- This module is DEPRECATED. Use "TypedRedex.Utils.Define" instead, which
-- provides a cleaner syntax with @concl@/@prem@ and matches paper notation better.
--
-- Migration guide:
--
-- @
-- -- Old (Rule.hs style):
-- stepAppL = rule2 \"step-app-l\" $ \\concl ->
--   fresh3 $ \\e1 e1' e2 -> do
--     concl (app e1 e2) (app e1' e2)
--     call (step e1 e1')
--
-- -- New (Define.hs style):
-- stepAppL = rule2 \"step-app-l\" $ fresh3 $ \\e1 e1' e2 -> do
--   concl $ step (app e1 e2) (app e1' e2)
--   prem  $ step e1 e1'
-- @
--
-- The Define.hs approach uses @judgment@ combinators to group rules:
--
-- @
-- step = judgment2 \"step\" [stepBeta, stepAppL, stepAppR]
-- @

module TypedRedex.Utils.Rule
  ( -- * Rule combinators
    rule
  , rule2
  , rule3
  , rule4
  , rule5
    -- * Axiom combinators (rules with no premises)
  , axiom
  , axiom2
  , axiom3
  , axiom4
    -- * Combining multiple rules
  , rules
  , rules2
  , rules3
  , rules4
  ) where

import TypedRedex.Core.Internal.Redex
import TypedRedex.Core.Internal.Logic
import TypedRedex.Utils.Fresh (L)
import TypedRedex.Utils.Relation (relation, relation2, relation3, relation4, relation5, call, conde, (<=>))

-- | Define a unary relation using inference-rule style.
rule :: (Redex rel, LogicType a)
     => String
     -> ((L a rel -> rel ()) -> rel ())
     -> L a rel -> Relation rel
rule name body = relation name $ \x ->
  body $ \px -> x <=> px

-- | Define a binary relation using inference-rule style.
--
-- @
-- stepAppL = rule2 \"app-L\" $ \\concl ->
--   fresh3 $ \\e1 e1' e2 -> do
--     concl (app e1 e2) (app e1' e2)
--     call (step e1 e1')
-- @
--
-- corresponds to:
--
-- @
--     e₁ ⟶ e₁'
-- ─────────────────
-- e₁ e₂ ⟶ e₁' e₂
-- @
rule2 :: (Redex rel, LogicType a, LogicType b)
      => String
      -> ((L a rel -> L b rel -> rel ()) -> rel ())
      -> L a rel -> L b rel -> Relation rel
rule2 name body = relation2 name $ \x y ->
  body $ \px py -> x <=> px >> y <=> py

-- | Define a ternary relation using inference-rule style.
rule3 :: (Redex rel, LogicType a, LogicType b, LogicType c)
      => String
      -> ((L a rel -> L b rel -> L c rel -> rel ()) -> rel ())
      -> L a rel -> L b rel -> L c rel -> Relation rel
rule3 name body = relation3 name $ \x y z ->
  body $ \px py pz -> x <=> px >> y <=> py >> z <=> pz

-- | Define a quaternary relation using inference-rule style.
rule4 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d)
      => String
      -> ((L a rel -> L b rel -> L c rel -> L d rel -> rel ()) -> rel ())
      -> L a rel -> L b rel -> L c rel -> L d rel -> Relation rel
rule4 name body = relation4 name $ \x y z w ->
  body $ \px py pz pw -> x <=> px >> y <=> py >> z <=> pz >> w <=> pw

-- | Define a 5-ary relation using inference-rule style.
rule5 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d, LogicType e)
      => String
      -> ((L a rel -> L b rel -> L c rel -> L d rel -> L e rel -> rel ()) -> rel ())
      -> L a rel -> L b rel -> L c rel -> L d rel -> L e rel -> Relation rel
rule5 name body = relation5 name $ \x y z w v ->
  body $ \px py pz pw pv -> x <=> px >> y <=> py >> z <=> pz >> w <=> pw >> v <=> pv

-- | Define an axiom (rule with no premises) for a unary relation.
axiom :: (Redex rel, LogicType a)
      => String
      -> L a rel
      -> L a rel -> Relation rel
axiom name px = rule name $ \concl -> concl px

-- | Define an axiom for a binary relation.
--
-- @
-- stepPredZero = axiom2 \"pred-zero\" (predTm zero) zero
-- @
axiom2 :: (Redex rel, LogicType a, LogicType b)
       => String
       -> L a rel -> L b rel
       -> L a rel -> L b rel -> Relation rel
axiom2 name px py = rule2 name $ \concl -> concl px py

-- | Define an axiom for a ternary relation.
axiom3 :: (Redex rel, LogicType a, LogicType b, LogicType c)
       => String
       -> L a rel -> L b rel -> L c rel
       -> L a rel -> L b rel -> L c rel -> Relation rel
axiom3 name px py pz = rule3 name $ \concl -> concl px py pz

-- | Define an axiom for a quaternary relation.
axiom4 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d)
       => String
       -> L a rel -> L b rel -> L c rel -> L d rel
       -> L a rel -> L b rel -> L c rel -> L d rel -> Relation rel
axiom4 name px py pz pw = rule4 name $ \concl -> concl px py pz pw

-- | Combine multiple unary rules into one relation.
--
-- @
-- value = rules "value" [valueLam, valueZero, valueSucc]
-- @
rules :: (Redex rel, LogicType a)
      => String
      -> [L a rel -> Relation rel]
      -> L a rel -> Relation rel
rules name rs = relation name $ \x ->
  conde [call (r x) | r <- rs]

-- | Combine multiple binary rules into one relation.
--
-- @
-- step = rules2 "step"
--   [ stepBeta
--   , stepAppL
--   , stepAppR
--   , ...
--   ]
-- @
rules2 :: (Redex rel, LogicType a, LogicType b)
       => String
       -> [L a rel -> L b rel -> Relation rel]
       -> L a rel -> L b rel -> Relation rel
rules2 name rs = relation2 name $ \x y ->
  conde [call (r x y) | r <- rs]

-- | Combine multiple ternary rules into one relation.
--
-- @
-- subst0 = rules3 "subst0"
--   [ subst0Lam
--   , subst0Var0
--   , subst0App
--   , ...
--   ]
-- @
rules3 :: (Redex rel, LogicType a, LogicType b, LogicType c)
       => String
       -> [L a rel -> L b rel -> L c rel -> Relation rel]
       -> L a rel -> L b rel -> L c rel -> Relation rel
rules3 name rs = relation3 name $ \x y z ->
  conde [call (r x y z) | r <- rs]

-- | Combine multiple quaternary rules into one relation.
rules4 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d)
       => String
       -> [L a rel -> L b rel -> L c rel -> L d rel -> Relation rel]
       -> L a rel -> L b rel -> L c rel -> L d rel -> Relation rel
rules4 name rs = relation4 name $ \x y z w ->
  conde [call (r x y z w) | r <- rs]
