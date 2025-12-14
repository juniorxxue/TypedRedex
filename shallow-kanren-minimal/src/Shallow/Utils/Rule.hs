{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ApplicativeDo #-}

-- | Inference-rule-style syntax for defining relations.
--
-- This module provides combinators that make relation definitions look
-- more like inference rules from papers:
--
-- @
--     e₁ ⟶ e₁'
-- ─────────────────── [step-app-l]
-- e₁ e₂ ⟶ e₁' e₂
-- @
--
-- becomes:
--
-- @
-- stepAppL = rule2 \"step-app-l\" $ \\match result ->
--   fresh3 $ \\e1 e1' e2 ->
--     match (app e1 e2) *>          -- input pattern
--     call (step e1 e1') *>         -- premise
--     result (app e1' e2)           -- output pattern
-- @
--
-- The @match@ function unifies with the first argument (input),
-- and @result@ unifies with the second argument (output).
-- This ensures patterns are matched BEFORE premises are evaluated.

module Shallow.Utils.Rule
  ( -- * Rule combinators (match/result style)
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
  ) where

import Shallow.Core.Internal.Kanren
import Shallow.Core.Internal.Logic
import Shallow.Utils.Kanren

-- | Define a unary relation using inference-rule style.
--
-- @
-- isZero = rule \"is-zero\" $ \\match ->
--   match zero
-- @
rule :: (Kanren rel, LogicType a)
     => String
     -> ((L a rel -> rel ()) -> rel ())
     -> L a rel -> Relation rel
rule name body = relation name $ \x ->
  body $ \px -> x <=> px

-- | Define a binary relation using inference-rule style.
--
-- Example (step relation for application left):
--
-- @
-- stepAppL = rule2 \"step-app-l\" $ \\match result ->
--   fresh3 $ \\e1 e1' e2 ->
--     match (app e1 e2) *>          -- input pattern (matched first!)
--     call (step e1 e1') *>         -- premise
--     result (app e1' e2)           -- output pattern
-- @
--
-- This corresponds to the inference rule:
--
-- @
--     e₁ ⟶ e₁'
-- ─────────────────
-- e₁ e₂ ⟶ e₁' e₂
-- @
--
-- The key insight: @match@ unifies FIRST, constraining fresh variables
-- before premises are evaluated. This prevents infinite search.
rule2 :: (Kanren rel, LogicType a, LogicType b)
      => String
      -> ((L a rel -> rel ()) -> (L b rel -> rel ()) -> rel ())
      -> L a rel -> L b rel -> Relation rel
rule2 name body = relation2 name $ \x y ->
  body (\px -> x <=> px) (\py -> y <=> py)

-- | Define a ternary relation using inference-rule style.
rule3 :: (Kanren rel, LogicType a, LogicType b, LogicType c)
      => String
      -> ((L a rel -> rel ()) -> (L b rel -> rel ()) -> (L c rel -> rel ()) -> rel ())
      -> L a rel -> L b rel -> L c rel -> Relation rel
rule3 name body = relation3 name $ \x y z ->
  body (\px -> x <=> px) (\py -> y <=> py) (\pz -> z <=> pz)

-- | Define a quaternary relation using inference-rule style.
rule4 :: (Kanren rel, LogicType a, LogicType b, LogicType c, LogicType d)
      => String
      -> ((L a rel -> rel ()) -> (L b rel -> rel ()) -> (L c rel -> rel ()) -> (L d rel -> rel ()) -> rel ())
      -> L a rel -> L b rel -> L c rel -> L d rel -> Relation rel
rule4 name body = relation4 name $ \x y z w ->
  body (\px -> x <=> px) (\py -> y <=> py) (\pz -> z <=> pz) (\pw -> w <=> pw)

-- | Define a 5-ary relation using inference-rule style.
rule5 :: (Kanren rel, LogicType a, LogicType b, LogicType c, LogicType d, LogicType e)
      => String
      -> ((L a rel -> rel ()) -> (L b rel -> rel ()) -> (L c rel -> rel ()) -> (L d rel -> rel ()) -> (L e rel -> rel ()) -> rel ())
      -> L a rel -> L b rel -> L c rel -> L d rel -> L e rel -> Relation rel
rule5 name body = relation5 name $ \x y z w v ->
  body (\px -> x <=> px) (\py -> y <=> py) (\pz -> z <=> pz) (\pw -> w <=> pw) (\pv -> v <=> pv)

-- | Define an axiom (rule with no premises) for a unary relation.
--
-- @
-- isUnit = axiom \"is-unit\" unit
-- @
axiom :: (Kanren rel, LogicType a)
      => String
      -> L a rel
      -> L a rel -> Relation rel
axiom name px = rule name $ \match -> match px

-- | Define an axiom for a binary relation.
--
-- @
-- stepPredZero = axiom2 \"pred-zero\" (predTm zero) zero
-- @
--
-- This corresponds to the axiom:
--
-- @
-- ─────────────────
-- pred(0) ⟶ 0
-- @
axiom2 :: (Kanren rel, LogicType a, LogicType b)
       => String
       -> L a rel -> L b rel
       -> L a rel -> L b rel -> Relation rel
axiom2 name px py = rule2 name $ \match result -> match px *> result py

-- | Define an axiom for a ternary relation.
axiom3 :: (Kanren rel, LogicType a, LogicType b, LogicType c)
       => String
       -> L a rel -> L b rel -> L c rel
       -> L a rel -> L b rel -> L c rel -> Relation rel
axiom3 name px py pz = rule3 name $ \mx my mz -> mx px *> my py *> mz pz

-- | Define an axiom for a quaternary relation.
axiom4 :: (Kanren rel, LogicType a, LogicType b, LogicType c, LogicType d)
       => String
       -> L a rel -> L b rel -> L c rel -> L d rel
       -> L a rel -> L b rel -> L c rel -> L d rel -> Relation rel
axiom4 name px py pz pw = rule4 name $ \mx my mz mw -> mx px *> my py *> mz pz *> mw pw
