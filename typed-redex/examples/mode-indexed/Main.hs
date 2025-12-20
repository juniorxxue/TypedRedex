{-# LANGUAGE QualifiedDo #-}

module Main (main) where

import qualified IndexedRule as R
import IndexedRule
  ( Rule
  , concl
  , fresh
  , h
  , p
  , prem
  , q
  , rule
  )

-- This rule typechecks even though:
--   1) 'prem (q y)' appears before 'prem (p x y)'
--   2) 'concl' is last
--
-- because a schedule exists:
--   concl grounds x; then p can run (needs x, produces y); then q y.
good =
  rule $ R.do
    x <- fresh
    y <- fresh
    prem (q y)
    prem (p x y)
    concl (h x)

-- Uncomment to see a compile-time mode error:

-- bad =
--   rule $ R.do
--     x <- fresh
--     y <- fresh
--     prem (q y)      -- q needs y ground...
--     concl (h x)     -- ...but concl only grounds x, and no premise produces y.

main :: IO ()
main = do
  -- Nothing interesting happens at runtime; this demo is about compile-time checks.
  putStrLn "mode-indexed demo: compiled OK (see good/bad in examples/mode-indexed/Main.hs)"
