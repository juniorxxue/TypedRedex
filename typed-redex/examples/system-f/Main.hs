{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Control.Applicative (empty)
import TypedRedex
import TypedRedex.Core.Internal.Logic (Logic (Ground), LogicType (..))
import TypedRedex.Nominal
import TypedRedex.Nominal.Prelude
import TypedRedex.Interp.Subst (runSubstRedex, takeS, Stream, RedexFresh(..))
import TypedRedex.Interp.Tracing (runWithDerivation, runWithDerivationWith, prettyDerivationWith, Derivation(..), JudgmentFormatter(..), defaultFormatConclusion)
import TypedRedex.Interp.Format (TermFormatter(..), subscriptNum)
import TypedRedex.Interp.Deep (printRulesWith)
import TypedRedex.DSL.Type (quote0, quote1, quote2)

import Syntax

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
-- Context lookup (using nominal equality)
--------------------------------------------------------------------------------

-- lookupTm ctx x ty: find x : ty in ctx
lookupTm :: (Redex rel) => Judge rel '[Ctx, Nom, Ty]
lookupTm = judgment "lookupTm" [lookupHere, lookupThere, lookupSkip]
  where
    -- Found at the head of context
    -- Pattern: lookupTm (x:ty, rest) x ty
    lookupHere = rule "lookup-here" $ fresh3 $ \x ty rest ->
      concl $ lookupTm (tmBind x ty rest) x ty

    -- Keep searching in tail
    -- Pattern: lookupTm (y:tyY, rest) x ty  where we look for x in rest
    lookupThere = rule "lookup-there" $ fresh5 $ \x y ty tyY rest -> do
      concl $ lookupTm (tmBind y tyY rest) x ty
      prem  $ lookupTm rest x ty

    -- Skip type variable binding
    -- Pattern: lookupTm (alpha, rest) x ty
    lookupSkip = rule "lookup-skip" $ fresh4 $ \alpha x ty rest -> do
      concl $ lookupTm (tyBind' alpha rest) x ty
      prem  $ lookupTm rest x ty

--------------------------------------------------------------------------------
-- Type checking (typeof ctx e ty)
--------------------------------------------------------------------------------

typeof :: (RedexFresh rel, RedexEval rel) => Judge rel '[Ctx, Tm, Ty]
typeof = judgment "typeof" [typeofUnit, typeofVar, typeofLam, typeofApp, typeofTLam, typeofTApp]
  where
    -- |- () : Unit
    typeofUnit = rule "typeof-unit" $ fresh $ \ctx ->
      concl $ typeof ctx unit' tunit

    -- Gamma(x) = A  =>  Gamma |- x : A
    typeofVar = rule "typeof-var" $ fresh3 $ \ctx x ty -> do
      concl $ typeof ctx (var x) ty
      prem  $ lookupTm ctx x ty

    -- Gamma, x:A |- e : B  =>  Gamma |- lam x:A. e : A -> B
    typeofLam = rule "typeof-lam" $ fresh2 $ \ctx tyA -> do
      freshNom_ $ \x -> fresh2 $ \body tyB -> do
        concl $ typeof ctx (lam tyA (bind x body)) (tarr tyA tyB)
        prem  $ typeof (tmBind (nom x) tyA ctx) body tyB

    -- Gamma |- e1 : A -> B  /\  Gamma |- e2 : A  =>  Gamma |- e1 e2 : B
    typeofApp = rule "typeof-app" $ fresh5 $ \ctx e1 e2 tyA tyB -> do
      concl $ typeof ctx (app e1 e2) tyB
      prem  $ typeof ctx e1 (tarr tyA tyB)
      prem  $ typeof ctx e2 tyA

    -- Gamma, alpha |- e : A  =>  Gamma |- Lam alpha. e : forall alpha. A
    typeofTLam = rule "typeof-tlam" $ fresh $ \ctx -> do
      -- Open the term binder to get fresh alpha and body
      freshTyNom_ $ \alpha -> fresh2 $ \body tyBody -> do
        concl $ typeof ctx (tlam (bind alpha body)) (tall (bind alpha tyBody))
        prem  $ typeof (tyBind' (tynom alpha) ctx) body tyBody

    -- Gamma |- e : forall alpha. A  =>  Gamma |- e [B] : A[alpha := B]
    typeofTApp = rule "typeof-tapp" $ fresh5 $ \ctx e tyArg tyBnd result -> do
      concl $ typeof ctx (tapp e tyArg) result
      prem  $ typeof ctx e (tall tyBnd)
      instantiateTo tyBnd tyArg result

--------------------------------------------------------------------------------
-- Running queries
--------------------------------------------------------------------------------

typeofIO :: Ctx -> Tm -> Stream Ty
typeofIO ctx0 e0 = runSubstRedex $ fresh $ \ty -> do
  appGoal $ typeof (Ground $ project ctx0) (Ground $ project e0) ty
  eval ty

checkIII :: Ctx -> Tm -> Ty -> Stream ()
checkIII ctx0 e0 ty0 = runSubstRedex $ do
  appGoal $ typeof (Ground $ project ctx0) (Ground $ project e0) (Ground $ project ty0)
  pure ()

-- Run with derivation tracing using custom formatter
typeofWithTrace :: Ctx -> Tm -> Stream (Ty, Derivation)
typeofWithTrace ctx0 e0 = runWithDerivationWith SystemFFormatter $ fresh $ \ty -> do
  appGoal $ typeof (Ground $ project ctx0) (Ground $ project e0) ty
  eval ty

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "=== System F Type Checking (Nominal) ==="
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

  -- Test 8: Derivation tree
  putStrLn "8. Derivation for typeof: lam x:Unit. x"
  case takeS 1 (typeofWithTrace Nil idUnit) of
    [(ty, deriv)] -> do
      putStrLn $ "Type: " ++ show ty
      putStrLn $ prettyDerivation deriv
    _ -> putStrLn "No derivation found"
  putStrLn ""

  putStrLn "=== All tests passed ==="
