{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}

-- | System F Type Checking with mode-checked rules.
--
-- This example demonstrates how to use the moded DSL with nominal features
-- for compile-time verification that all rules have valid execution schedules.
--
-- Includes SubstRedex and TracingRedex interpreters.
module Main (main) where

import Control.Monad (forM_)
import TypedRedex
import TypedRedex.Nominal
import TypedRedex.Nominal.Prelude
import TypedRedex.Interp.Subst (runSubstRedex, takeS, Stream)
import TypedRedex.Interp.Tracing (runWithDerivationWith, prettyDerivationWith, Derivation(..), JudgmentFormatter(..), defaultFormatConclusion)
import TypedRedex.Interp.Typesetting (runTypesettingWith, formatRule, typesettingVar)
import TypedRedex.Interp.Format (TermFormatter(..))
import TypedRedex.Nominal.Bind (mkBind)
import TypedRedex.DSL.Fresh (LTerm)
import qualified TypedRedex.DSL.Fresh as F
import TypedRedex.DSL.Moded (AppliedM(..), toApplied, ground)

import Syntax
import Rules

--------------------------------------------------------------------------------
-- Judgment Formatter for System F
--------------------------------------------------------------------------------

-- | Custom formatter for System F derivations
data SystemFFormatter = SystemFFormatter

instance JudgmentFormatter SystemFFormatter where
  formatJudgment _ name args = case (name, args) of
    -- Typing judgment
    ("typeof", [ctx, e, ty]) -> ctx ++ " |- " ++ e ++ " : " ++ ty
    (n, [ctx, e, ty]) | "typeof-" `isPrefixOf` n -> ctx ++ " |- " ++ e ++ " : " ++ ty
    -- Context lookup
    ("lookupTm", [ctx, n, ty]) -> ctx ++ "(" ++ n ++ ") = " ++ ty
    (n, [ctx, idx, ty]) | "lookup" `isPrefixOf` n -> ctx ++ "(" ++ idx ++ ") = " ++ ty
    -- Type substitution: [tyArg/alpha]tyBody = result
    ("substTy", [alpha, tyArg, tyBody, result]) -> "[" ++ tyArg ++ "/" ++ alpha ++ "]" ++ tyBody ++ " = " ++ result
    (n, [alpha, tyArg, tyBody, result]) | "subst" `isPrefixOf` n -> "[" ++ tyArg ++ "/" ++ alpha ++ "]" ++ tyBody ++ " = " ++ result
    -- Default
    _ -> defaultFormatConclusion name args
    where
      isPrefixOf [] _ = True
      isPrefixOf _ [] = False
      isPrefixOf (x:xs) (y:ys) = x == y && isPrefixOf xs ys

-- | TermFormatter for nice System F term display
instance TermFormatter SystemFFormatter where
  formatTerm _ name args = case (name, args) of
    -- Terms
    ("App", [f, a]) -> Just $ "(" ++ f ++ " " ++ a ++ ")"
    -- Lam: extract var from Bind format "var.body" and format as (λvar:ty. body)
    ("Lam", [ty, b]) ->
      let (var, rest) = break (== '.') b
      in Just $ "(λ" ++ var ++ ":" ++ ty ++ ". " ++ drop 1 rest ++ ")"
    ("Var", [n]) -> Just n
    ("Unit", []) -> Just "()"
    -- TLam: extract var from Bind format "var.body" and format as (Λvar. body)
    ("TLam", [b]) ->
      let (var, rest) = break (== '.') b
      in Just $ "(Λ" ++ var ++ ". " ++ drop 1 rest ++ ")"
    ("TApp", [e, ty]) -> Just $ "(" ++ e ++ " [" ++ ty ++ "])"
    -- Types
    ("TUnit", []) -> Just "Unit"
    ("TVar", [n]) -> Just n
    ("TArr", [a, b]) -> Just $ "(" ++ a ++ " → " ++ b ++ ")"
    -- TAll: extract var from Bind format "var.body" and format as (∀var. body)
    ("TAll", [b]) ->
      let (var, rest) = break (== '.') b
      in Just $ "(∀" ++ var ++ ". " ++ drop 1 rest ++ ")"
    -- Binders: output "var.body" format for parent to parse
    ("Bind", [n, body]) -> Just $ n ++ "." ++ body
    -- Contexts
    ("Nil", []) -> Just "·"
    ("TmBind", [n, ty, ctx]) -> Just $ ctx ++ ", " ++ n ++ ":" ++ ty
    ("TyBind'", [alpha, ctx]) -> Just $ ctx ++ ", " ++ alpha
    -- Nominal atoms
    ('x':rest, []) | all isDigit rest -> Just $ "x" ++ subscriptDigits rest
    ('a':rest, []) | all isDigit rest -> Just $ "α" ++ subscriptDigits rest
    _ -> Nothing
    where
      isDigit c = c `elem` "0123456789"
      subscriptDigits = map toSubscript
      toSubscript '0' = '₀'; toSubscript '1' = '₁'; toSubscript '2' = '₂'
      toSubscript '3' = '₃'; toSubscript '4' = '₄'; toSubscript '5' = '₅'
      toSubscript '6' = '₆'; toSubscript '7' = '₇'; toSubscript '8' = '₈'
      toSubscript '9' = '₉'; toSubscript c = c

-- | Pretty-print derivation with System F formatting
prettyDerivation :: Derivation -> String
prettyDerivation = prettyDerivationWith SystemFFormatter

--------------------------------------------------------------------------------
-- Running queries
--------------------------------------------------------------------------------

-- SubstRedex: typeof in mode (I,I,O)
typeofIO :: Ctx -> Tm -> Stream Ty
typeofIO ctx0 e0 = runSubstRedex $ F.fresh $ \ty -> do
  let ctxL = Ground $ project ctx0
      eL   = Ground $ project e0
  appGoal $ toApplied $ typeof (ground ctxL) (ground eL) (ground ty)
  eval ty

-- SubstRedex: verification mode (I,I,I)
checkIII :: Ctx -> Tm -> Ty -> Stream ()
checkIII ctx0 e0 ty0 = runSubstRedex $ do
  let ctxL = Ground $ project ctx0
      eL   = Ground $ project e0
      tyL  = Ground $ project ty0
  appGoal $ toApplied $ typeof (ground ctxL) (ground eL) (ground tyL)
  pure ()

-- TracingRedex: typeof with derivation tree
type TracingStream a = Stream (a, Derivation)

typeofWithTrace :: Ctx -> Tm -> TracingStream Ty
typeofWithTrace ctx0 e0 = runWithDerivationWith SystemFFormatter $ F.fresh $ \ty -> do
  let ctxL = Ground $ project ctx0
      eL   = Ground $ project e0
  appGoal $ toApplied $ typeof (ground ctxL) (ground eL) (ground ty)
  eval ty

--------------------------------------------------------------------------------
-- Typesetting Interpreter: Rule Extraction
--------------------------------------------------------------------------------

-- | Extract and print typeof rules using typesetting interpreter
printTypeofRules :: IO ()
printTypeofRules = do
  let rules = runTypesettingWith SystemFFormatter $ do
        appGoal $ toApplied $ typeof (ground (typesettingVar 0)) (ground (typesettingVar 1)) (ground (typesettingVar 2))
  mapM_ (\r -> putStrLn (formatRule SystemFFormatter "typeof" r) >> putStrLn "") rules

-- | Extract and print lookupTm rules using typesetting interpreter
printLookupRules :: IO ()
printLookupRules = do
  let rules = runTypesettingWith SystemFFormatter $ do
        appGoal $ toApplied $ lookupTm (ground (typesettingVar 0)) (ground (typesettingVar 1)) (ground (typesettingVar 2))
  mapM_ (\r -> putStrLn (formatRule SystemFFormatter "lookupTm" r) >> putStrLn "") rules

-- | Extract and print substTy rules using typesetting interpreter
printSubstTyRules :: IO ()
printSubstTyRules = do
  let rules = runTypesettingWith SystemFFormatter $ do
        appGoal $ toApplied $ substTy (ground (typesettingVar 0)) (ground (typesettingVar 1)) (ground (typesettingVar 2)) (ground (typesettingVar 3))
  mapM_ (\r -> putStrLn (formatRule SystemFFormatter "substTy" r) >> putStrLn "") rules

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "==============================================================================="
  putStrLn "=== System F Typing Rules (Typesetting Interpreter) ==="
  putStrLn "==============================================================================="
  putStrLn ""
  putStrLn "The typesetting interpreter extracts inference rules from the relation definitions."
  putStrLn "These are the rules themselves, as you would write in a paper:"
  putStrLn ""

  putStrLn "--- typeof rules ---"
  putStrLn ""
  printTypeofRules

  putStrLn "--- substTy rules ---"
  putStrLn ""
  printSubstTyRules

  putStrLn "--- lookupTm rules ---"
  putStrLn ""
  printLookupRules

  putStrLn "==============================================================================="
  putStrLn "=== System F Type Checking (Execution) ==="
  putStrLn "==============================================================================="
  putStrLn ""

  -- Test 1: Simple type check
  putStrLn "1. Typecheck: ()"
  print $ takeS 1 (typeofIO Nil Unit)
  putStrLn ""

  -- Test 2: Identity on Unit
  let x10 = Nom 10
      idUnit = Lam TUnit (Bind x10 (Var x10))
  putStrLn "2. Typecheck: lam x:Unit. x"
  print $ takeS 1 (typeofIO Nil idUnit)
  putStrLn ""

  -- Test 3: Application
  let appTerm = App idUnit Unit
  putStrLn "3. Typecheck: (lam x:Unit. x) ()"
  print $ takeS 1 (typeofIO Nil appTerm)
  putStrLn ""

  -- Test 4: Polymorphic identity
  let alpha10 = TyNom 10
      x20 = Nom 20
      polyId = TLam (Bind alpha10 (Lam (TVar alpha10) (Bind x20 (Var x20))))
  putStrLn "4. Typecheck: Lam alpha. lam x:alpha. x"
  putStrLn $ "   Term: " ++ show polyId
  let polyIdResult = takeS 1 (typeofIO Nil polyId)
  print polyIdResult
  putStrLn ""

  -- Test 5: Type application
  let polyIdApp = TApp polyId TUnit
  putStrLn "5. Typecheck: (Lam alpha. lam x:alpha. x) [Unit]"
  print $ takeS 1 (typeofIO Nil polyIdApp)
  putStrLn ""

  -- Test 6: Nested lambda
  let x1 = Nom 1
      x2 = Nom 2
      constUnit = Lam TUnit (Bind x1 (Lam TUnit (Bind x2 (Var x1))))
  putStrLn "6. Typecheck: lam x:Unit. lam y:Unit. x"
  print $ takeS 1 (typeofIO Nil constUnit)
  putStrLn ""

  -- Test 7: Apply specialized identity to a value
  -- (polyId [Unit]) () : Unit
  let polyIdUnitApp = App (TApp polyId TUnit) Unit
  putStrLn "7. Typecheck: ((Lam alpha. lam x:alpha. x) [Unit]) ()"
  print $ takeS 1 (typeofIO Nil polyIdUnitApp)
  putStrLn ""

  putStrLn "=== Derivation Trees (TracingRedex) ==="
  putStrLn ""

  -- Derivation 1: lam x:Unit. x
  putStrLn "Derivation: lam x:Unit. x"
  case takeS 1 (typeofWithTrace Nil idUnit) of
    [(ty, deriv)] -> do
      putStrLn $ "Type: " ++ show ty
      putStrLn $ prettyDerivation deriv
    _ -> putStrLn "No derivation found"

  -- Derivation 2: (lam x:Unit. x) ()
  putStrLn "Derivation: (lam x:Unit. x) ()"
  case takeS 1 (typeofWithTrace Nil appTerm) of
    [(ty, deriv)] -> do
      putStrLn $ "Type: " ++ show ty
      putStrLn $ prettyDerivation deriv
    _ -> putStrLn "No derivation found"

  putStrLn "=== Mode Checking Guarantee ==="
  putStrLn ""
  putStrLn "All rules compile, proving mode correctness:"
  putStrLn "  - lookupTm (I,I,O): ctx and name ground -> type output"
  putStrLn "  - typeof (I,I,O): ctx and term ground -> type output"
  putStrLn ""
  putStrLn "Key moded DSL features for nominal logic:"
  putStrLn "  - fresh: creates tracked logic variables (for pattern matching)"
  putStrLn "  - bindNomPatM/bindTyPatM: binder patterns with logic variable names"
  putStrLn "  - liftRel: lifts rel actions like instantiateTo into RuleM"
  putStrLn ""

  putStrLn "==============================================================================="
  putStrLn "=== ALPHA-EQUIVALENCE TEST ==="
  putStrLn "==============================================================================="
  putStrLn ""

  -- Test: fresh a b c x y; a = \x.x; c = \y.b; a == c; b == Var y
  let xN = Nom 1
      yN = Nom 2

  putStrLn "Test: fresh a b c; a = \\x.x; c = \\y.b; a == c; b == Var y"
  let test :: Stream Tm
      test = runSubstRedex $ F.fresh3 $ \a c b -> do
        a <=> Ground (project (Lam TUnit (Bind xN (Var xN))))  -- a = \x. x
        c <=> lamL (Ground (project TUnit)) (mkBind yN b)      -- c = \y. b  (b is logic var)
        a <=> c                                                 -- a == c
        b <=> Ground (project (Var yN))                         -- b == Var y
        eval b
  putStrLn $ "Result: " ++ show (takeS 1 test)
  putStrLn ""

  putStrLn "==============================================================================="
  putStrLn "=== RUNTIME SCHEDULING PROOF ==="
  putStrLn "==============================================================================="
  putStrLn ""
  putStrLn "The following tests compare 'typeof' (normal premise order) with"
  putStrLn "'typeof' (deliberately WRONG premise order)."
  putStrLn ""
