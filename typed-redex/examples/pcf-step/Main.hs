{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import TypedRedex
import TypedRedex.Core.Internal.Logic (Logic (Ground, Free), LogicType (..))
import TypedRedex.Interp.Subst (runSubstRedex, takeS, Stream)
import TypedRedex.Interp.Deep (runDeepWith, formatRule)
import TypedRedex.Interp.Tracing (runWithDerivationWith, prettyDerivationWith, substInDerivation, Derivation(..), JudgmentFormatter(..), defaultFormatConclusion)
import TypedRedex.Interp.Format (TermFormatter(..), subscriptNum)
import TypedRedex.DSL.Fresh (LTerm)
import qualified TypedRedex.DSL.Fresh as F
import TypedRedex.DSL.Moded (AppliedM(..), toApplied, ground)

import Rules

-- PCF (Programming Computable Functions) with fixpoints
-- Small-step call-by-value operational semantics
--
-- Mode-checked version using the moded DSL.

--------------------------------------------------------------------------------
-- Judgment Formatter for PCF
--------------------------------------------------------------------------------

-- | Custom formatter for PCF derivations
data PCFFormatter = PCFFormatter

instance JudgmentFormatter PCFFormatter where
  formatJudgment _ name args = case (name, args) of
    -- Step relation
    ("step", [a, b]) -> a ++ " ⟶ " ++ b
    -- Step rules (all binary step rules)
    (n, [a, b]) | n `elem` stepRules -> a ++ " ⟶ " ++ b
    -- Value predicate
    ("value", [a]) -> "value(" ++ a ++ ")"
    (n, [a]) | "value" `isPrefixOf` n -> "value(" ++ a ++ ")"
    -- Substitution
    ("subst0", [body, arg, result]) -> "[" ++ arg ++ "/0]" ++ body ++ " = " ++ result
    (n, [body, arg, result]) | "subst0" `isPrefixOf` n -> "[" ++ arg ++ "/0]" ++ body ++ " = " ++ result
    -- Default
    _ -> defaultFormatConclusion name args
    where
      stepRules = ["β", "app-L", "app-R", "succ", "pred", "pred-zero", "pred-succ", "ifz", "ifz-zero", "ifz-succ", "fix"]

      isPrefixOf [] _ = True
      isPrefixOf _ [] = False
      isPrefixOf (x:xs) (y:ys) = x == y && isPrefixOf xs ys

-- | TermFormatter for nice PCF term display
instance TermFormatter PCFFormatter where
  formatTerm _ name args = case (name, args) of
    -- Application
    ("App", [f, a]) -> Just $ "(" ++ f ++ " " ++ a ++ ")"
    -- Lambda
    ("Lam", [b]) -> Just $ "(λ." ++ b ++ ")"
    -- Variables
    ("Var", [n]) -> Just $ parseAndShowVar n
    -- Naturals
    ("Zero", []) -> Just "0"
    ("Succ", [e]) -> Just $ "S(" ++ e ++ ")"
    ("Pred", [e]) -> Just $ "pred(" ++ e ++ ")"
    ("Ifz", [c, t, f]) -> Just $ "ifz(" ++ c ++ ", " ++ t ++ ", " ++ f ++ ")"
    ("Fix", [e]) -> Just $ "fix(" ++ e ++ ")"
    ("Z", []) -> Just "0"
    ("S", [n]) -> Just $ "S(" ++ n ++ ")"
    _ -> Nothing
    where
      parseAndShowVar n = case parseNat n of
        Just k  -> "x" ++ subscriptNum (show k)
        Nothing -> n
      parseNat "0" = Just 0
      parseNat ('S':'(':rest) = case parseNat (init rest) of
        Just k -> Just (k + 1)
        Nothing -> Nothing
      parseNat s | all isDigit s = Just (read s)
      parseNat _ = Nothing
      isDigit c = c `elem` "0123456789"

-- | Pretty-print derivation with PCF formatting
prettyDerivation :: Derivation -> String
prettyDerivation = prettyDerivationWith PCFFormatter

--------------------------------------------------------------------------------
-- Running queries
--------------------------------------------------------------------------------

-- Run step in mode (I,O) using SubstRedex
stepIO :: Tm -> Stream Tm
stepIO t0 = runSubstRedex $ F.fresh $ \t' -> do
  appGoal $ toApplied $ step (ground $ Ground $ project t0) (ground t')
  eval t'

-- Run step with derivation tracing using TracingRedex
type TracingStream a = Stream (a, Derivation)

stepWithTrace :: Tm -> TracingStream Tm
stepWithTrace t0 = runWithDerivationWith PCFFormatter $ F.fresh $ \t' -> do
  appGoal $ toApplied $ step (ground $ Ground $ project t0) (ground t')
  eval t'

-- Extract rules using DeepRedex
printStepRules :: IO ()
printStepRules = do
  let rules = runDeepWith PCFFormatter $ do
        appGoal $ toApplied $ step (ground $ Free undefined) (ground $ Free undefined)
  mapM_ (putStrLn . formatRule PCFFormatter "step") rules

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "=== Automatic Rule Extraction (DeepRedex) ==="
  putStrLn ""

  -- Extract all step rules automatically
  printStepRules

  putStrLn ""
  putStrLn "=== PCF Small-Step Semantics (Execution) ==="
  putStrLn ""

  -- Example 1: pred(succ(0)) → 0
  let ex1 = Pred (Succ Zero)
  putStrLn "Step: pred(succ(0))"
  print $ takeS 3 (stepIO ex1)
  putStrLn ""

  -- Example 2: ifz(0, succ(0), pred(0)) → succ(0)
  let ex2 = Ifz Zero (Succ Zero) (Pred Zero)
  putStrLn "Step: ifz(0, succ(0), pred(0))"
  print $ takeS 1 (stepIO ex2)
  putStrLn ""

  -- Example 3: Application (λx.x) 0 → 0
  let ex3 = App (Lam (Var Z)) Zero
  putStrLn "Step: (λx.x) 0"
  print $ takeS 1 (stepIO ex3)
  putStrLn ""

  putStrLn "=== Derivation Trees (TracingRedex) ==="
  putStrLn ""

  -- Example 1: pred(succ(0)) → 0
  putStrLn "Example 1: pred(succ(0)) → 0"
  putStrLn "Expected: pred-succ rule with value premise"
  case takeS 1 (stepWithTrace ex1) of
    [(result, deriv)] -> do
      let deriv' = substInDerivation "x0" (showTm result) deriv
      putStrLn $ prettyDerivation deriv'
    _ -> putStrLn "No derivation found"

  -- Example 2: (λx.x) 0 → 0
  putStrLn "Example 2: (λx.x) 0 → 0"
  putStrLn "Expected: β rule with value and subst0 premises"
  case takeS 1 (stepWithTrace ex3) of
    [(result, deriv)] -> do
      let deriv' = substInDerivation "x0" (showTm result) deriv
      putStrLn $ prettyDerivation deriv'
    _ -> putStrLn "No derivation found"

  -- Example 3: succ(pred(succ(0))) → succ(0)
  let ex4 = Succ (Pred (Succ Zero))
  putStrLn "Example 3: succ(pred(succ(0))) → succ(0)"
  putStrLn "Expected: succ congruence with nested pred-succ"
  case takeS 1 (stepWithTrace ex4) of
    [(result, deriv)] -> do
      let deriv' = substInDerivation "x0" (showTm result) deriv
      putStrLn $ prettyDerivation deriv'
    _ -> putStrLn "No derivation found"

  -- Example 4: fix(λf.λx.x) → (λf.λx.x) fix(λf.λx.x)
  let ex5 = Fix (Lam (Lam (Var Z)))
  putStrLn "Example 4: fix(λf.λx.x) → (λf.λx.x) fix(λf.λx.x)"
  putStrLn "Expected: fix unrolling (axiom)"
  case takeS 1 (stepWithTrace ex5) of
    [(result, deriv)] -> do
      let deriv' = substInDerivation "x0" (showTm result) deriv
      putStrLn $ prettyDerivation deriv'
    _ -> putStrLn "No derivation found"

  putStrLn "=== Mode Checking Guarantee ==="
  putStrLn ""
  putStrLn "All rules compile, proving mode correctness:"
  putStrLn "  - value (I): term is input (predicate)"
  putStrLn "  - subst0 (I,I,O): body and arg are inputs, result is output"
  putStrLn "  - step (I,O): before is input, after is output"
  putStrLn ""

-- Helper to show a term nicely
showTm :: Tm -> String
showTm Zero = "0"
showTm (Succ e) = "succ(" ++ showTm e ++ ")"
showTm (Pred e) = "pred(" ++ showTm e ++ ")"
showTm (Var Z) = "x"
showTm (Var (S n)) = "y" ++ show (natToInt n)
showTm (Lam b) = "(λ." ++ showTm b ++ ")"
showTm (App f a) = "(" ++ showTm f ++ " " ++ showTm a ++ ")"
showTm (Ifz c t e) = "ifz(" ++ showTm c ++ ", " ++ showTm t ++ ", " ++ showTm e ++ ")"
showTm (Fix e) = "fix(" ++ showTm e ++ ")"

natToInt :: Nat -> Int
natToInt Z = 0
natToInt (S n) = 1 + natToInt n
