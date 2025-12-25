{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}

-- | Bidirectional STLC with mode-checked rules.
--
-- This example demonstrates how to use the moded DSL for compile-time
-- verification that all rules have valid execution schedules.
--
-- Includes all three interpreters: SubstRedex, TracingRedex, TypesettingRedex
module Main (main) where

import TypedRedex
import TypedRedex.Interp.Subst (runSubstRedex, takeS, Stream)
import TypedRedex.Interp.Typesetting (runTypesettingWith, formatRule, typesettingVar)
import TypedRedex.Interp.Tracing (runWithDerivationWith, prettyDerivationWith, Derivation(..), JudgmentFormatter(..), defaultFormatConclusion)
import TypedRedex.Interp.Format (TermFormatter(..), subscriptNum)
import TypedRedex.DSL.Fresh (LTerm)
import qualified TypedRedex.DSL.Fresh as F
import TypedRedex.DSL.Moded (AppliedM(..), toApplied, ground)

import Rules

--------------------------------------------------------------------------------
-- Judgment Formatter for Bidirectional STLC
--------------------------------------------------------------------------------

-- | Custom formatter for bidirectional typing derivations
data BidirFormatter = BidirFormatter

instance JudgmentFormatter BidirFormatter where
  formatJudgment _ name args = case (name, args) of
    -- Synthesis rules (start with ⇒)
    (n, [ctx, e, ty]) | isSynthRule n -> ctx ++ " ⊢ " ++ e ++ " ⇒ " ++ ty
    -- Checking rules (start with ⇐)
    (n, [ctx, e, ty]) | isCheckRule n -> ctx ++ " ⊢ " ++ e ++ " ⇐ " ++ ty
    -- Context lookup
    (n, [ctx, idx, ty]) | isLookupRule n -> ctx ++ "(" ++ idx ++ ") = " ++ ty
    -- Default
    _ -> defaultFormatConclusion name args
    where
      isSynthRule ('⇒':_) = True
      isSynthRule s = "synth" `isPrefixOf` s
      isCheckRule ('⇐':_) = True
      isCheckRule s = "check" `isPrefixOf` s
      isLookupRule s = "lookup" `isPrefixOf` s
      isPrefixOf [] _ = True
      isPrefixOf _ [] = False
      isPrefixOf (x:xs) (y:ys) = x == y && isPrefixOf xs ys

-- | TermFormatter for nice term display
instance TermFormatter BidirFormatter where
  formatTerm _ name args = case (name, args) of
    -- Application
    ("App", [f, a]) -> Just $ "(" ++ f ++ " " ++ a ++ ")"
    -- Lambda (unannotated)
    ("λ", [b]) -> Just $ "(λ." ++ b ++ ")"
    -- Lambda (annotated)
    ("λ:", [ty, b]) -> Just $ "(λ:" ++ ty ++ ". " ++ b ++ ")"
    -- Annotation
    (":", [e, ty]) -> Just $ "(" ++ e ++ " : " ++ ty ++ ")"
    -- Variables
    ("Var", [n]) -> Just $ parseAndShowVar n
    -- Unit
    ("()", []) -> Just "()"
    -- Types
    ("Unit", []) -> Just "Unit"
    ("→", [a, b]) -> Just $ "(" ++ a ++ " → " ++ b ++ ")"
    -- Contexts
    ("·", []) -> Just "·"
    (",", [ty, ctx]) -> Just $ ctx ++ ", " ++ ty
    -- Naturals
    ("Z", []) -> Just "0"
    ("S", [n]) -> Just $ "S(" ++ n ++ ")"
    _ -> Nothing
    where
      parseAndShowVar n = case parseNat n of
        Just k  -> "x" ++ subscriptNum k
        Nothing -> n
      parseNat "0" = Just 0
      parseNat ('S':'(':rest) = case parseNat (init rest) of
        Just k -> Just (k + 1)
        Nothing -> Nothing
      parseNat s | all isDigit s = Just (read s)
      parseNat _ = Nothing
      isDigit c = c `elem` "0123456789"

-- | Pretty-print derivation with bidirectional typing formatting
prettyDerivation :: Derivation -> String
prettyDerivation = prettyDerivationWith BidirFormatter

--------------------------------------------------------------------------------
-- Running queries
--------------------------------------------------------------------------------

-- SubstRedex: synthesis in mode (I,I,O)
synthIO :: Ctx -> Tm -> Stream Ty
synthIO ctx0 e0 = runSubstRedex $ F.fresh $ \ty -> do
  let ctxL = Ground $ project ctx0
      eL   = Ground $ project e0
  appGoal $ toApplied $ synth (ground ctxL) (ground eL) (ground ty)
  eval ty

-- SubstRedex: checking in mode (I,I,I)
checkIII :: Ctx -> Tm -> Ty -> Stream ()
checkIII ctx0 e0 ty0 = runSubstRedex $ do
  let ctxL = Ground $ project ctx0
      eL   = Ground $ project e0
      tyL  = Ground $ project ty0
  appGoal $ toApplied $ check (ground ctxL) (ground eL) (ground tyL)
  pure ()

-- SubstRedex: notInCtx in mode (I,I) - uses negation-as-failure
notInCtxIO :: Ctx -> Nat -> Stream ()
notInCtxIO ctx0 n0 = runSubstRedex $ do
  let ctxL = Ground $ project ctx0
      nL   = Ground $ project n0
  appGoal $ toApplied $ notInCtx (ground ctxL) (ground nL)
  pure ()

-- TracingRedex: synthesis with derivation tree
type TracingStream a = Stream (a, Derivation)

synthWithTrace :: Ctx -> Tm -> TracingStream Ty
synthWithTrace ctx0 e0 = runWithDerivationWith BidirFormatter $ F.fresh $ \ty -> do
  let ctxL = Ground $ project ctx0
      eL   = Ground $ project e0
  appGoal $ toApplied $ synth (ground ctxL) (ground eL) (ground ty)
  eval ty

-- TracingRedex: checking with derivation tree
checkWithTrace :: Ctx -> Tm -> Ty -> TracingStream ()
checkWithTrace ctx0 e0 ty0 = runWithDerivationWith BidirFormatter $ do
  let ctxL = Ground $ project ctx0
      eL   = Ground $ project e0
      tyL  = Ground $ project ty0
  appGoal $ toApplied $ check (ground ctxL) (ground eL) (ground tyL)
  pure ()

-- TypesettingRedex: extract rules
printSynthRules :: IO ()
printSynthRules = do
  let rules = runTypesettingWith BidirFormatter $ do
        appGoal $ toApplied $ synth (ground (typesettingVar 0)) (ground (typesettingVar 1)) (ground (typesettingVar 2))
  mapM_ (putStrLn . formatRule BidirFormatter "synth") rules

printCheckRules :: IO ()
printCheckRules = do
  let rules = runTypesettingWith BidirFormatter $ do
        appGoal $ toApplied $ check (ground (typesettingVar 0)) (ground (typesettingVar 1)) (ground (typesettingVar 2))
  mapM_ (putStrLn . formatRule BidirFormatter "check") rules

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "=== Automatic Rule Extraction (TypesettingRedex) ==="
  putStrLn ""

  putStrLn "Synth rules:"
  printSynthRules
  putStrLn ""

  putStrLn "Check rules:"
  printCheckRules
  putStrLn ""

  putStrLn "=== Mode-Checked Bidirectional STLC (Execution) ==="
  putStrLn ""

  -- Example 1: Synthesize λx:Unit. x
  let ex1 = LamAnn TUnit (Var Z)
  putStrLn "1. Synthesize λx:Unit. x"
  print $ takeS 1 (synthIO Nil ex1)
  putStrLn ""

  -- Example 2: Synthesize ((λx. x) : Unit → Unit)
  let ex2 = Ann (Lam (Var Z)) (TArr TUnit TUnit)
  putStrLn "2. Synthesize ((λx. x) : Unit → Unit)"
  print $ takeS 1 (synthIO Nil ex2)
  putStrLn ""

  -- Example 3: Check λx. x ⇐ Unit → Unit
  let ex3 = Lam (Var Z)
  putStrLn "3. Check λx. x ⇐ Unit → Unit"
  print $ takeS 1 (checkIII Nil ex3 (TArr TUnit TUnit))
  putStrLn ""

  -- Example 4: Application
  let ex4 = App (Ann (Lam (Var Z)) (TArr TUnit TUnit)) Unit
  putStrLn "4. Synthesize ((λx. x) : Unit → Unit) ()"
  print $ takeS 1 (synthIO Nil ex4)
  putStrLn ""

  putStrLn "=== Derivation Trees (TracingRedex) ==="
  putStrLn ""

  -- Derivation 1: λf:Unit→Unit. λx:Unit. f x
  let ex5 = LamAnn (TArr TUnit TUnit) (LamAnn TUnit (App (Var (S Z)) (Var Z)))
  putStrLn "Derivation: λf:Unit→Unit. λx:Unit. f x"
  putStrLn "Expected: Nested ⇒λ: with ⇒App, lookup"
  case takeS 1 (synthWithTrace Nil ex5) of
    [(ty, deriv)] -> do
      putStrLn $ "Type: " ++ show ty
      putStrLn $ prettyDerivation deriv
    _ -> putStrLn "No derivation found"

  -- Derivation 2: ((λx. x) : Unit → Unit) ()
  putStrLn "Derivation: ((λx. x) : Unit → Unit) ()"
  putStrLn "Expected: ⇒App with ⇒Ann and ⇐Sub"
  case takeS 1 (synthWithTrace Nil ex4) of
    [(ty, deriv)] -> do
      putStrLn $ "Type: " ++ show ty
      putStrLn $ prettyDerivation deriv
    _ -> putStrLn "No derivation found"

  putStrLn "=== Mode Checking Guarantee ==="
  putStrLn ""
  putStrLn "All rules compile, proving mode correctness:"
  putStrLn "  - lookup (I,I,O): ctx and index ground → type output"
  putStrLn "  - synth (I,I,O): ctx and term ground → type output"
  putStrLn "  - check (I,I,I): all positions ground (verification)"
  putStrLn ""

  putStrLn "=== Negation-as-Failure Example ==="
  putStrLn ""

  -- notInCtx: succeeds if index is NOT in context
  let ctx1 = Cons TUnit Nil  -- ctx = [Unit], indices 0 is valid
  putStrLn "Testing notInCtx with ctx = [Unit]:"

  -- Index 0 IS in context, so notInCtx should fail (no results)
  putStrLn "  notInCtx [Unit] 0 → (should fail)"
  print $ takeS 1 (notInCtxIO ctx1 Z)

  -- Index 1 is NOT in context (out of bounds), so notInCtx should succeed
  putStrLn "  notInCtx [Unit] 1 → (should succeed)"
  print $ takeS 1 (notInCtxIO ctx1 (S Z))

  -- Index 2 is NOT in context, so notInCtx should succeed
  putStrLn "  notInCtx [Unit] 2 → (should succeed)"
  print $ takeS 1 (notInCtxIO ctx1 (S (S Z)))

  -- Empty context: any index is not in it
  putStrLn "  notInCtx [] 0 → (should succeed, empty ctx)"
  print $ takeS 1 (notInCtxIO Nil Z)
  putStrLn ""
