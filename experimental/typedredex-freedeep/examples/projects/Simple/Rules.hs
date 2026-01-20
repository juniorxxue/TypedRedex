{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RebindableSyntax #-}

module Simple.Rules (add) where

import Data.String (fromString)
import Prelude hiding ((>>=), (>>), return)
import qualified Prelude as P
import TypedRedex.DSL
import TypedRedex.Pretty ((<+>))

import Simple.Syntax (Nat, zro, suc)

add :: Judgment "add" '[I, I, O] '[Nat, Nat, Nat]
add = judgment $
  format (\x y z -> x <+> " + " <+> y <+> " = " <+> z)
  P.>> rules
    [ rule "add-zero" $ do
        y <- fresh
        concl $ add zro y y

    , rule "add-succ" $ do
        (x, y, z) <- fresh
        concl $ add (suc x) y (suc z)
        prem  $ add x y z
    ]
