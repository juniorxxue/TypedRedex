{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}

-- | Test for negation static checking.
--
-- This Main imports NegRules which has:
-- - GOOD: notInCtx2 (compiles)
-- - BAD: badCheck (commented out - uncomment to see error)
module Main where

import TypedRedex
import TypedRedex.Core.Internal.Logic (Logic (Ground))
import TypedRedex.Interp.Subst (runSubstRedex, takeS)
import TypedRedex.DSL.Moded (AppliedM(..), toApplied, ground)

-- Import rules
import Rules (Nat(..), Ctx(..), Ty(..), nil, cons)
import NegRules (notInCtx2)

-- Helper to run notInCtx2
notInCtx2IO :: Ctx -> Nat -> [()]
notInCtx2IO ctx n = takeS 10 $ runSubstRedex $ do
  let ctxL = Ground $ project ctx
      nL = Ground $ project n
  appGoal $ toApplied $ notInCtx2 (ground ctxL) (ground nL)

main :: IO ()
main = do
  let ctx1 = Cons TUnit Nil  -- [Unit]

  putStrLn "=== Static Check for Negation Demo ==="
  putStrLn ""

  putStrLn "Testing notInCtx2 (GOOD - compiles because all vars grounded):"
  putStrLn $ "  notInCtx2 [Unit] 0 → " ++ show (notInCtx2IO ctx1 Z) ++ " (should be [], 0 IS in ctx)"
  putStrLn $ "  notInCtx2 [Unit] 1 → " ++ show (notInCtx2IO ctx1 (S Z)) ++ " (should be [()], 1 NOT in ctx)"
  putStrLn $ "  notInCtx2 [] 0 → " ++ show (notInCtx2IO Nil Z) ++ " (should be [()], empty ctx)"
  putStrLn ""

  putStrLn "=== To see compile-time error ==="
  putStrLn "Uncomment 'badCheck' in NegRules.hs to see:"
  putStrLn ""
  putStrLn "  Negation error in \"badCheck\":"
  putStrLn "    grounded after premises: '[0, 1]"
  putStrLn "    negation needs: [0, 1, 2]"
  putStrLn "    missing: '[2]"
