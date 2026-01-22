{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RebindableSyntax #-}

module Pcf.Rules
  ( add
  , evalP
  ) where

import Prelude hiding ((>>=), (>>), return)
import TypedRedex.DSL

import Pcf.Syntax

--------------------------------------------------------------------------------
-- Judgments
--------------------------------------------------------------------------------

add :: Judgment "add" '[I, I, O] '[Tm, Tm, Tm]
add = judgment
  [ rule "add-zero" $ do
      y <- fresh
      concl $ add zero y y

  , rule "add-succ" $ do
      (x, y, z) <- fresh
      concl $ add (succTm x) y (succTm z)
      prem  $ add x y z
  ]

evalP :: Judgment "eval" '[I, O] '[Tm, Tm]
evalP = judgment
  [ rule "eval-zero" $ do
      concl $ evalP zero zero

  , rule "eval-succ" $ do
      (t, v) <- fresh
      concl $ evalP (succTm t) (succTm v)
      prem  $ evalP t v

  , rule "eval-pred-zero" $ do
      concl $ evalP (predTm zero) zero

  , rule "eval-pred-succ" $ do
      (t, v) <- fresh
      concl $ evalP (predTm (succTm t)) v
      prem  $ evalP t v

  , rule "eval-if0-zero" $ do
      (t, t1, t2, v) <- fresh
      concl $ evalP (if0 t t1 t2) v
      prem  $ evalP t zero
      prem  $ evalP t1 v

  , rule "eval-if0-succ" $ do
      (t, n, t1, t2, v) <- fresh
      concl $ evalP (if0 t t1 t2) v
      prem  $ evalP t (succTm n)
      prem  $ evalP t2 v

  , rule "eval-plus" $ do
      (t1, t2, v1, v2, v) <- fresh
      concl $ evalP (plus t1 t2) v
      prem  $ evalP t1 v1
      prem  $ evalP t2 v2
      prem  $ add v1 v2 v
  ]
