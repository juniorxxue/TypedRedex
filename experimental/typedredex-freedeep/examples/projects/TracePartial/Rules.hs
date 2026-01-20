{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RebindableSyntax #-}

module TracePartial.Rules
  ( g
  , h
  , neqDemo
  ) where

import Data.String (fromString)
import Prelude hiding ((>>=), (>>), return)
import qualified Prelude as P
import TypedRedex.DSL
import TypedRedex.Pretty ((<+>))

import TracePartial.Syntax (Nat)

--------------------------------------------------------------------------------
-- Tiny search-tree example (two-premise chain)
--------------------------------------------------------------------------------

g :: Judgment "g" '[I, O] '[Nat, Nat]
g = judgment $
  format (\x y -> x <+> " ~g~ " <+> y)
  P.>> rules
    [ rule "g-refl" $ do
        x <- fresh
        concl $ g x x
    ]

h :: Judgment "h" '[I, O] '[Nat, Nat]
h = judgment $
  format (\x y -> x <+> " ~h~ " <+> y)
  P.>> rules
    [ rule "h-chain" $ do
        (x, y, z) <- fresh
        concl $ h x z
        prem  $ g x y
        prem  $ g y z
    ]

neqDemo :: Judgment "neqDemo" '[I, I] '[Nat, Nat]
neqDemo = judgment $
  format (\x y -> x <+> " != " <+> y)
  P.>> rules
    [ rule "neq-demo" $ do
        (x, y) <- fresh
        concl $ neqDemo x y
        x =/= y
    ]
