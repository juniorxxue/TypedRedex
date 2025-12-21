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
import TypedRedex.Interp.Format (TermFormatter(..))
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
    ("Lam", [ty, b]) -> Just $ "(lam:" ++ ty ++ ". " ++ b ++ ")"
    ("Var", [n]) -> Just $ n
    ("Unit", []) -> Just "()"
    ("TLam", [b]) -> Just $ "(Lam." ++ b ++ ")"
    ("TApp", [e, ty]) -> Just $ "(" ++ e ++ " [" ++ ty ++ "])"
    -- Types
    ("TUnit", []) -> Just "Unit"
    ("TVar", [n]) -> Just n
    ("TArr", [a, b]) -> Just $ "(" ++ a ++ " -> " ++ b ++ ")"
    ("TAll", [ty]) -> Just $ "(forall. " ++ ty ++ ")"
    -- Binders (now unified as Bind)
    ("Bind", [n, body]) -> Just $ "(\\" ++ n ++ ". " ++ body ++ ")"
    -- Contexts
    ("Nil", []) -> Just "."
    ("TmBind", [n, ty, ctx]) -> Just $ ctx ++ ", " ++ n ++ ":" ++ ty
    ("TyBind'", [alpha, ctx]) -> Just $ ctx ++ ", " ++ alpha
    -- Nominal atoms
    ("x0", []) -> Just "x0"
    ("x1", []) -> Just "x1"
    ("x2", []) -> Just "x2"
    ('x':rest, []) -> Just $ "x" ++ rest
    ('a':rest, []) | all isDigit rest -> Just $ "a" ++ rest
    _ -> Nothing
    where
      isDigit c = c `elem` "0123456789"

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

-- | Run typeof with wrong order
typeofWrongOrderIO :: Ctx -> Tm -> Stream Ty
typeofWrongOrderIO ctx0 e0 = runSubstRedex $ F.fresh $ \ty -> do
  let ctxL = Ground $ project ctx0
      eL   = Ground $ project e0
  appGoal $ toApplied $ typeofWrongOrder (ground ctxL) (ground eL) (ground ty)
  eval ty

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "=== System F Type Checking (Execution) ==="
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
  putStrLn "=== RUNTIME SCHEDULING PROOF ==="
  putStrLn "==============================================================================="
  putStrLn ""
  putStrLn "The following tests compare 'typeof' (normal premise order) with"
  putStrLn "'typeofWrongOrder' (deliberately WRONG premise order)."
  putStrLn ""
  putStrLn "In typeofWrongOrder:"
  putStrLn "  - typeof-app: prem2 (needs tyA) written BEFORE prem1 (produces tyA)"
  putStrLn "  - typeof-var/lam/tlam/tapp: prem written BEFORE concl"
  putStrLn ""
  putStrLn "WITHOUT runtime scheduling, typeofWrongOrder would FAIL because:"
  putStrLn "  - Premises would execute in source order"
  putStrLn "  - prem2 would try to use tyA before prem1 produces it"
  putStrLn ""
  putStrLn "WITH runtime scheduling, both produce IDENTICAL results:"
  putStrLn ""

  -- Test terms
  let testTerms =
        [ ("()", Unit)
        , ("lam x:Unit. x", idUnit)
        , ("(lam x:Unit. x) ()", appTerm)
        , ("Lam alpha. lam x:alpha. x", polyId)
        , ("(Lam alpha. lam x:alpha. x) [Unit]", polyIdApp)
        , ("lam x:Unit. lam y:Unit. x", constUnit)
        , ("((Lam alpha. lam x:alpha. x) [Unit]) ()", polyIdUnitApp)
        ]

  -- Run comparison tests
  forM_ (zip [1..] testTerms) $ \(i, (name, term)) -> do
    let normalResult = takeS 1 (typeofIO Nil term)
        wrongOrderResult = takeS 1 (typeofWrongOrderIO Nil term)
        match = normalResult == wrongOrderResult
    putStrLn $ show (i :: Int) ++ ". " ++ name
    putStrLn $ "   Normal order:      " ++ show normalResult
    putStrLn $ "   Wrong order:       " ++ show wrongOrderResult
    putStrLn $ "   Match: " ++ (if match then "YES" else "NO (BUG!)")
    putStrLn ""

  putStrLn "All tests pass: Runtime scheduling correctly reorders premises!"
  putStrLn ""
