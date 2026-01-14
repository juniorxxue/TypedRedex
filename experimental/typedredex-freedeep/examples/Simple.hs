{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Simple example: Natural numbers with addition
module Main where

import qualified TypedRedex.DSL as R
import TypedRedex.DSL
import TypedRedex.Interp.Typeset

--------------------------------------------------------------------------------
-- Syntax: Natural numbers
--------------------------------------------------------------------------------

-- | Natural numbers
data Nat = Z | S Nat
  deriving (Eq, Show)

instance Repr Nat where
  -- Reified representation
  data Reified Nat = RZ | RS (Logic Nat)

  project Z     = RZ
  project (S n) = RS (Ground (project n))

  reify RZ         = Just Z
  reify (RS (Ground r)) = S <$> reify r
  reify _          = Nothing

  quote RZ     = ("Z", [])
  quote (RS n) = ("S", [Field n])

-- Smart constructors
zro :: Term '[] Nat
zro = ground Z

suc :: Term vs Nat -> Term vs Nat
suc = lift1 (\n -> Ground (RS n))

--------------------------------------------------------------------------------
-- Judgment: add(X, Y, Z) — X + Y = Z
--------------------------------------------------------------------------------

add :: Judgment "add" '[I, I, O] '[Nat, Nat, Nat]
add = judgment
  [ -- add(Z, Y, Y)
    rule "add-zero" $ R.do
      y <- R.freshVar @Nat
      R.concl $ add # (zro, y, y)

  , -- add(S(X), Y, S(Z)) :- add(X, Y, Z)
    rule "add-succ" $ R.do
      x <- R.freshVar @Nat
      y <- R.freshVar @Nat
      z <- R.freshVar @Nat
      R.concl $ add # (suc x, y, suc z)
      R.prem  $ add # (x, y, z)
  ]

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "=== TypedRedex FreeDeep Example ==="
  putStrLn ""

  -- Typeset the add judgment
  putStrLn $ typeset (add # (zro, zro, zro))

  putStrLn "=== Done ==="
