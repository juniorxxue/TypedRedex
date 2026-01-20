{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RebindableSyntax #-}

module ModeErrors.Rules
  ( f
  , bad
  ) where

import Prelude hiding ((>>=), (>>), return)
import TypedRedex.DSL

import ModeErrors.Syntax (Nat, zro)

f :: Judgment "f" '[I, O] '[Nat, Nat]
f = judgment
  [ rule "f-base" $ do
      (x, y) <- fresh
      concl $ f x y
  ]

bad :: Judgment "bad" '[I, O] '[Nat, Nat]
bad = judgment
  [ rule "bad-ghost" $ do
      ghost <- fresh
      out <- fresh
      concl $ bad zro out
      prem  $ f ghost out
  ]
