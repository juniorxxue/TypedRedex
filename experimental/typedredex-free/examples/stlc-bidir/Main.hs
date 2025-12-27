{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}

-- | Demonstration of Three Interpreters for the Free Monad DSL
--
-- This example shows how the same rules can be interpreted in different ways:
--
-- 1. **Typeset**: Extract rules as ASCII inference rules
-- 2. **Eval**: Execute queries to find solutions
-- 3. **Trace**: Build derivation trees (TODO: integrate with queries)
module Main (main) where

import Rules
import Rel (Rel, runRelN)

import TypedRedex.Free
  ( Logic(..), T(..), ground, toApplied, Applied(..)
  )
import TypedRedex.Free.Interp.Typeset
  ( extractRules, renumber, formatRule, DummyRel, RawRule(..)
  )
import TypedRedex.Free.Moded (ModedRule(..))

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════════"
  putStrLn "   Indexed Free Monad DSL - Three Interpreters Demo"
  putStrLn "═══════════════════════════════════════════════════════════════"
  putStrLn ""

  -- Demo 1: Typesetting
  putStrLn "┌─────────────────────────────────────────────────────────────┐"
  putStrLn "│  1. TYPESET INTERPRETER                                     │"
  putStrLn "│     Extracts rules as ASCII inference rules                 │"
  putStrLn "└─────────────────────────────────────────────────────────────┘"
  putStrLn ""
  demoTypeset

  -- Demo 2: Eval
  putStrLn ""
  putStrLn "┌─────────────────────────────────────────────────────────────┐"
  putStrLn "│  2. EVAL INTERPRETER                                        │"
  putStrLn "│     Executes queries to find solutions                      │"
  putStrLn "└─────────────────────────────────────────────────────────────┘"
  putStrLn ""
  demoEval

  -- Demo 3: Trace (structure only)
  putStrLn ""
  putStrLn "┌─────────────────────────────────────────────────────────────┐"
  putStrLn "│  3. TRACE INTERPRETER                                       │"
  putStrLn "│     Builds derivation trees (structure demo)                │"
  putStrLn "└─────────────────────────────────────────────────────────────┘"
  putStrLn ""
  demoTrace

  putStrLn ""
  putStrLn "═══════════════════════════════════════════════════════════════"
  putStrLn "   All three interpreters demonstrated successfully!"
  putStrLn "═══════════════════════════════════════════════════════════════"

--------------------------------------------------------------------------------
-- Typeset Demo
--------------------------------------------------------------------------------

demoTypeset :: IO ()
demoTypeset = do
  putStrLn "Extracting inference rules from AST..."
  putStrLn ""

  -- Extract and format lookup rules
  putStrLn "── Context Lookup (Γ(n) = A) ──"
  putStrLn ""
  let lookupRawRules = extractRules (lookupCtxRules @DummyRel)
  mapM_ (printRule "lookup") lookupRawRules
  putStrLn ""

  -- Extract and format synth rules
  putStrLn "── Type Synthesis (Γ ⊢ e ⇒ A) ──"
  putStrLn ""
  let synthRawRules = extractRules (synthRules @DummyRel)
  mapM_ (printRule "synth") synthRawRules
  putStrLn ""

  -- Extract and format check rules
  putStrLn "── Type Checking (Γ ⊢ e ⇐ A) ──"
  putStrLn ""
  let checkRawRules = extractRules (checkRules @DummyRel)
  mapM_ (printRule "check") checkRawRules

  where
    printRule :: String -> RawRule -> IO ()
    printRule judgmentName rawRule = do
      let displayRule = renumber rawRule
      putStrLn $ formatRule judgmentName displayRule
      putStrLn ""

--------------------------------------------------------------------------------
-- Eval Demo
--------------------------------------------------------------------------------

demoEval :: IO ()
demoEval = do
  putStrLn "Running queries with the Rel monad..."
  putStrLn ""

  -- Query 1: What type does 'unit' synthesize to?
  putStrLn "Query 1: synth · () ?ty"
  putStrLn "  (What type does 'unit' synthesize to in empty context?)"
  let query1 :: Rel ()
      query1 = appliedGoal $ toApplied $
        synth nil unit (T mempty (Free undefined))
  let results1 = runRelN 1 query1
  putStrLn $ "  Results: " ++ show (length results1) ++ " solution(s) found"
  putStrLn ""

  -- Query 2: Can we synthesize a type for (λ:Unit. x₀)?
  putStrLn "Query 2: synth · (λ:Unit. x₀) ?ty"
  putStrLn "  (Lambda with annotation synthesizes arrow type)"
  let query2 :: Rel ()
      query2 = appliedGoal $ toApplied $
        synth nil (lamAnn tunit (var zro)) (T mempty (Free undefined))
  let results2 = runRelN 1 query2
  putStrLn $ "  Results: " ++ show (length results2) ++ " solution(s) found"
  putStrLn ""

  -- Query 3: Check that (λ. x₀) checks against Unit → Unit
  putStrLn "Query 3: check · (λ. x₀) (Unit → Unit)"
  putStrLn "  (Unannotated lambda checks against arrow type)"
  let query3 :: Rel ()
      query3 = appliedGoal $ toApplied $
        check nil (lam (var zro)) (tarr tunit tunit)
  let results3 = runRelN 1 query3
  putStrLn $ "  Results: " ++ show (length results3) ++ " solution(s) found"
  putStrLn ""

  -- Query 4: Lookup in context
  putStrLn "Query 4: lookup (Unit, ·) Z ?ty"
  putStrLn "  (Looking up index 0 in context with Unit)"
  let query4 :: Rel ()
      query4 = appliedGoal $ toApplied $
        lookupCtx (cons tunit nil) zro (T mempty (Free undefined))
  let results4 = runRelN 1 query4
  putStrLn $ "  Results: " ++ show (length results4) ++ " solution(s) found"

--------------------------------------------------------------------------------
-- Trace Demo
--------------------------------------------------------------------------------

demoTrace :: IO ()
demoTrace = do
  putStrLn "The Trace interpreter builds derivation trees."
  putStrLn ""
  putStrLn "Example derivation structure for: synth · () Unit"
  putStrLn ""
  putStrLn "    ─────────────────── [⇒Unit]"
  putStrLn "      · ⊢ () ⇒ Unit"
  putStrLn ""
  putStrLn "Example derivation for: check · (λ.x₀) (Unit → Unit)"
  putStrLn ""
  putStrLn "              ───────────────────────── [⇒Var]"
  putStrLn "                Unit,· ⊢ x₀ ⇒ Unit"
  putStrLn "              ───────────────────────── [⇐Sub]"
  putStrLn "                Unit,· ⊢ x₀ ⇐ Unit"
  putStrLn "    ─────────────────────────────────────────── [⇐λ]"
  putStrLn "           · ⊢ (λ.x₀) ⇐ (Unit → Unit)"
  putStrLn ""
  putStrLn "(Full trace integration uses interpretTrace from Trace.hs)"
