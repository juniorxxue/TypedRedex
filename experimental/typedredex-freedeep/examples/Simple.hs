{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Simple example: Natural numbers with addition
module Main where

import qualified TypedRedex.DSL as R
import TypedRedex.DSL
import TypedRedex.Interp.Typeset
import TypedRedex.Pretty ((<+>))
import Support.Nat

--------------------------------------------------------------------------------
-- Judgment: add(X, Y, Z) — X + Y = Z
--------------------------------------------------------------------------------

add :: Judgment "add" '[I, I, O] '[Nat, Nat, Nat]
add = judgment $ do
  format $ \x y z -> x <+> " + " <+> y <+> " = " <+> z
  rules
    [ -- add(Z, Y, Y)
      rule "add-zero" $ R.do
        y <- R.fresh
        R.concl $ add zro y y

    , -- add(S(X), Y, S(Z)) :- add(X, Y, Z)
      rule "add-succ" $ R.do
        x <- R.fresh
        y <- R.fresh
        z <- R.fresh
        R.concl $ add (suc x) y (suc z)
        R.prem  $ add x y z
    ]

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "=== TypedRedex FreeDeep Example ==="
  putStrLn ""

  -- Typeset the add judgment
  putStrLn $ typeset (add zro zro zro)

  putStrLn "=== Done ==="
