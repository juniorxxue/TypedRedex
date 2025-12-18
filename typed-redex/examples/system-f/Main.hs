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
import TypedRedex.Interp.Subst (runSubstRedex, takeS, Stream)
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
    ("typeof", [ctx, e, ty]) -> ctx ++ " ⊢ " ++ e ++ " : " ++ ty
    (n, [ctx, e, ty]) | "typeof-" `isPrefixOf` n -> ctx ++ " ⊢ " ++ e ++ " : " ++ ty
    -- Context lookup
    ("lookupTm", [ctx, n, ty]) -> ctx ++ "(" ++ n ++ ") = " ++ ty
    ("lookup", [ctx, idx, ty]) -> ctx ++ "(" ++ idx ++ ") = " ++ ty
    (n, [ctx, idx, ty]) | "lookup" `isPrefixOf` n -> ctx ++ "(" ++ idx ++ ") = " ++ ty
    -- Nat comparison
    ("natLt", [n, m]) -> n ++ " < " ++ m
    (n, [a, b]) | "lt-" `isPrefixOf` n -> a ++ " < " ++ b
    ("natEq", [n, m]) -> n ++ " = " ++ m
    (n, [a, b]) | "eq-" `isPrefixOf` n -> a ++ " = " ++ b
    -- Addition
    ("addNat", [n, m, s]) -> n ++ " + " ++ m ++ " = " ++ s
    ("add", [a, b, c]) -> a ++ " + " ++ b ++ " = " ++ c
    (n, [a, b, c]) | "add-" `isPrefixOf` n -> a ++ " + " ++ b ++ " = " ++ c
    -- Type substitution (handles both "substTy" and "subst")
    ("substTy", [d, s, t, r]) -> "[" ++ s ++ "/" ++ d ++ "]" ++ t ++ " = " ++ r
    ("subst", [d, s, t, r]) -> "[" ++ s ++ "/" ++ d ++ "]" ++ t ++ " = " ++ r
    (n, [d, s, t, r]) | "subst-" `isPrefixOf` n -> "[" ++ s ++ "/" ++ d ++ "]" ++ t ++ " = " ++ r
    ("substTyVar", [d, s, v, r]) -> "[" ++ s ++ "/" ++ d ++ "](TVar " ++ v ++ ") = " ++ r
    -- Type shifting
    ("shiftTy", [c, a, t, r]) -> "↑" ++ superscript c ++ "·" ++ superscript a ++ " " ++ t ++ " = " ++ r
    ("shift", [c, a, t, r]) -> "↑" ++ superscript c ++ "·" ++ superscript a ++ " " ++ t ++ " = " ++ r
    (n, [c, a, t, r]) | "shift-" `isPrefixOf` n -> "↑" ++ superscript c ++ "·" ++ superscript a ++ " " ++ t ++ " = " ++ r
    ("shiftTyVar", [c, a, v, r]) -> "↑" ++ superscript c ++ "·" ++ superscript a ++ " (TVar " ++ v ++ ") = " ++ r
    -- Default
    _ -> defaultFormatConclusion name args
    where
      isPrefixOf [] _ = True
      isPrefixOf _ [] = False
      isPrefixOf (x:xs) (y:ys) = x == y && isPrefixOf xs ys

      superscript = map toSuper
        where
          toSuper '0' = '⁰'; toSuper '1' = '¹'; toSuper '2' = '²'; toSuper '3' = '³'
          toSuper '4' = '⁴'; toSuper '5' = '⁵'; toSuper '6' = '⁶'; toSuper '7' = '⁷'
          toSuper '8' = '⁸'; toSuper '9' = '⁹'; toSuper c = c

-- | TermFormatter for nice System F term display (for future use)
instance TermFormatter SystemFFormatter where
  formatTerm _ name args = case (name, args) of
    -- Terms
    ("App", [f, a]) -> Just $ "(" ++ f ++ " " ++ a ++ ")"
    ("Lam", [ty, b]) -> Just $ "(λ:" ++ ty ++ ". " ++ b ++ ")"
    ("Var", [n]) -> Just $ parseAndShowVar n
    ("Unit", []) -> Just "()"
    ("TLam", [b]) -> Just $ "(Λ." ++ b ++ ")"
    ("TApp", [e, ty]) -> Just $ "(" ++ e ++ " [" ++ ty ++ "])"
    -- Types
    ("TUnit", []) -> Just "Unit"
    ("TVar", [n]) -> Just $ "α" ++ subscriptNum n
    ("TArr", [a, b]) -> Just $ "(" ++ a ++ " → " ++ b ++ ")"
    ("TAll", [ty]) -> Just $ "(∀. " ++ ty ++ ")"
    -- Contexts
    ("Nil", []) -> Just "·"
    ("TmBind", [ty, ctx]) -> Just $ ctx ++ ", x:" ++ ty
    ("TyBind", [ctx]) -> Just $ ctx ++ ", α"
    -- Naturals
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

-- | Pretty-print derivation with System F formatting
prettyDerivation :: Derivation -> String
prettyDerivation = prettyDerivationWith SystemFFormatter

--------------------------------------------------------------------------------
-- Relations using the new judgment/rule syntax
--------------------------------------------------------------------------------

-- Nat equality check
natEq :: (Redex rel) => Judge rel '[Nat, Nat]
natEq = judgment "natEq" [natEqZero, natEqSucc]
  where
    natEqZero = rule "eq-zero" $
      concl $ natEq zro zro

    natEqSucc = rule "eq-succ" $ fresh2 $ \n' m' -> do
      concl $ natEq (suc n') (suc m')
      prem  $ natEq n' m'

-- Less than check (strict)
natLt :: (Redex rel) => Judge rel '[Nat, Nat]
natLt = judgment "natLt" [natLtZero, natLtSucc]
  where
    natLtZero = rule "lt-zero" $ fresh $ \m' ->
      concl $ natLt zro (suc m')

    natLtSucc = rule "lt-succ" $ fresh2 $ \n' m' -> do
      concl $ natLt (suc n') (suc m')
      prem  $ natLt n' m'

-- Context lookup
lookupTm :: (Redex rel) => Judge rel '[Ctx, Nat, Ty]
lookupTm = judgment "lookupTm" [lookupTmHere, lookupTmThere, lookupTmSkip]
  where
    lookupTmHere = rule "lookup-here" $ fresh2 $ \ty rest ->
      concl $ lookupTm (tmBind ty rest) zro ty

    lookupTmThere = rule "lookup-there" $ fresh4 $ \ty ty' rest n' -> do
      concl $ lookupTm (tmBind ty' rest) (suc n') ty
      prem  $ lookupTm rest n' ty

    lookupTmSkip = rule "lookup-skip" $ fresh3 $ \rest n ty -> do
      concl $ lookupTm (tyBind rest) n ty
      prem  $ lookupTm rest n ty

--------------------------------------------------------------------------------
-- Addition on natural numbers
--------------------------------------------------------------------------------

-- ───────────────────── [add-zero]
-- addNat 0 m m
--
-- addNat n m sum
-- ────────────────────────────── [add-succ]
-- addNat (S n) m (S sum)

addNat :: (Redex rel) => Judge rel '[Nat, Nat, Nat]
addNat = judgment "addNat" [addZero, addSucc]
  where
    addZero = rule "add-zero" $ fresh $ \m ->
      concl $ addNat zro m m

    addSucc = rule "add-succ" $ fresh3 $ \n' m sum' -> do
      concl $ addNat (suc n') m (suc sum')
      prem  $ addNat n' m sum'

--------------------------------------------------------------------------------
-- Type substitution (substTy depth subTy ty result)
--------------------------------------------------------------------------------

-- [subst-unit]
-- substTy depth subTy Unit Unit
--
-- substTyVar depth subTy n result
-- ─────────────────────────────────── [subst-var]
-- substTy depth subTy (TVar n) result
--
-- substTy depth subTy a a'   substTy depth subTy b b'
-- ───────────────────────────────────────────────────── [subst-arr]
-- substTy depth subTy (a → b) (a' → b')
--
-- substTy (S depth) subTy body body'
-- ─────────────────────────────────────────── [subst-all]
-- substTy depth subTy (∀.body) (∀.body')

substTy :: (Redex rel) => Judge rel '[Nat, Ty, Ty, Ty]
substTy = judgment "substTy" [substUnit, substVar, substArr, substAll]
  where
    substUnit = rule "subst-unit" $ fresh2 $ \depth subTy ->
      concl $ substTy depth subTy tunit tunit

    substVar = rule "subst-var" $ fresh3 $ \depth subTy n -> fresh $ \result -> do
      concl $ substTy depth subTy (tvar n) result
      prem  $ substTyVar depth subTy n result

    substArr = rule "subst-arr" $ fresh4 $ \depth subTy a b -> fresh2 $ \a' b' -> do
      concl $ substTy depth subTy (tarr a b) (tarr a' b')
      prem  $ substTy depth subTy a a'
      prem  $ substTy depth subTy b b'

    substAll = rule "subst-all" $ fresh3 $ \depth subTy body -> fresh $ \body' -> do
      concl $ substTy depth subTy (tall body) (tall body')
      prem  $ substTy (suc depth) subTy body body'

--------------------------------------------------------------------------------
-- Type substitution variable case (substTyVar depth subTy n result)
--------------------------------------------------------------------------------

-- n = depth
-- ────────────────────────────── [subst-var-eq]
-- substTyVar depth subTy n subTy
--
-- n < depth
-- ──────────────────────────────────── [subst-var-lt]
-- substTyVar depth subTy n (TVar n)
--
-- depth < n
-- ──────────────────────────────────────────── [subst-var-gt]
-- substTyVar depth subTy (S n') (TVar n')

substTyVar :: (Redex rel) => Judge rel '[Nat, Ty, Nat, Ty]
substTyVar = judgment "substTyVar" [substVarEq, substVarLt, substVarGt]
  where
    substVarEq = rule "subst-var-eq" $ fresh2 $ \depth subTy -> do
      concl $ substTyVar depth subTy depth subTy

    substVarLt = rule "subst-var-lt" $ fresh3 $ \depth subTy n -> do
      concl $ substTyVar depth subTy n (tvar n)
      prem  $ natLt n depth

    substVarGt = rule "subst-var-gt" $ fresh3 $ \depth subTy n' -> do
      concl $ substTyVar depth subTy (suc n') (tvar n')
      prem  $ natLt depth (suc n')

--------------------------------------------------------------------------------
-- Type shifting (shiftTy cutoff amount ty result)
--------------------------------------------------------------------------------

-- ─────────────────────────────── [shift-unit]
-- shiftTy cutoff amount Unit Unit
--
-- shiftTyVar cutoff amount n result
-- ────────────────────────────────────── [shift-var]
-- shiftTy cutoff amount (TVar n) result
--
-- shiftTy cutoff amount a a'   shiftTy cutoff amount b b'
-- ────────────────────────────────────────────────────────── [shift-arr]
-- shiftTy cutoff amount (a → b) (a' → b')
--
-- shiftTy (S cutoff) amount body body'
-- ─────────────────────────────────────────────── [shift-all]
-- shiftTy cutoff amount (∀.body) (∀.body')

shiftTy :: (Redex rel) => Judge rel '[Nat, Nat, Ty, Ty]
shiftTy = judgment "shiftTy" [shiftUnit, shiftVar, shiftArr, shiftAll]
  where
    shiftUnit = rule "shift-unit" $ fresh2 $ \cutoff amount ->
      concl $ shiftTy cutoff amount tunit tunit

    shiftVar = rule "shift-var" $ fresh3 $ \cutoff amount n -> fresh $ \result -> do
      concl $ shiftTy cutoff amount (tvar n) result
      prem  $ shiftTyVar cutoff amount n result

    shiftArr = rule "shift-arr" $ fresh4 $ \cutoff amount a b -> fresh2 $ \a' b' -> do
      concl $ shiftTy cutoff amount (tarr a b) (tarr a' b')
      prem  $ shiftTy cutoff amount a a'
      prem  $ shiftTy cutoff amount b b'

    shiftAll = rule "shift-all" $ fresh3 $ \cutoff amount body -> fresh $ \body' -> do
      concl $ shiftTy cutoff amount (tall body) (tall body')
      prem  $ shiftTy (suc cutoff) amount body body'

--------------------------------------------------------------------------------
-- Type shifting variable case (shiftTyVar cutoff amount n result)
--------------------------------------------------------------------------------

-- n < cutoff
-- ────────────────────────────────────── [shift-var-lt]
-- shiftTyVar cutoff amount n (TVar n)
--
-- n >= cutoff   addNat n amount n'
-- ─────────────────────────────────────── [shift-var-ge]
-- shiftTyVar cutoff amount n (TVar n')

shiftTyVar :: (Redex rel) => Judge rel '[Nat, Nat, Nat, Ty]
shiftTyVar = judgment "shiftTyVar" [shiftVarLt, shiftVarGeEq, shiftVarGeGt]
  where
    -- n < cutoff: keep variable unchanged
    shiftVarLt = rule "shift-var-lt" $ fresh3 $ \cutoff amount n -> do
      concl $ shiftTyVar cutoff amount n (tvar n)
      prem  $ natLt n cutoff

    -- n = cutoff: shift by amount
    shiftVarGeEq = rule "shift-var-eq" $ fresh3 $ \cutoff amount n' -> do
      concl $ shiftTyVar cutoff amount cutoff (tvar n')
      prem  $ addNat cutoff amount n'

    -- n > cutoff: shift by amount
    shiftVarGeGt = rule "shift-var-gt" $ fresh4 $ \cutoff amount n n' -> do
      concl $ shiftTyVar cutoff amount n (tvar n')
      prem  $ natLt cutoff n
      prem  $ addNat n amount n'

--------------------------------------------------------------------------------
-- Type checking (typeof ctx e ty)
--------------------------------------------------------------------------------

-- ─────────────────────── [typeof-unit]
-- typeof ctx () Unit
--
-- lookupTm ctx n ty
-- ─────────────────────── [typeof-var]
-- typeof ctx (var n) ty
--
-- typeof (tmBind tyA ctx) body tyB
-- ──────────────────────────────────────────── [typeof-lam]
-- typeof ctx (λ:tyA. body) (tyA → tyB)
--
-- typeof ctx e1 (tyA → ty)   typeof ctx e2 tyA
-- ──────────────────────────────────────────── [typeof-app]
-- typeof ctx (e1 e2) ty
--
-- typeof (tyBind ctx) body tyA
-- ──────────────────────────────────── [typeof-tlam]
-- typeof ctx (Λ. body) (∀. tyA)
--
-- typeof ctx e (∀. tyA)   substTy 0 tyB tyA tyA'
-- ─────────────────────────────────────────────── [typeof-tapp]
-- typeof ctx (e [tyB]) tyA'

typeof :: (Redex rel) => Judge rel '[Ctx, Tm, Ty]
typeof = judgment "typeof" [typeofUnit, typeofVar, typeofLam, typeofApp, typeofTLam, typeofTApp]
  where
    typeofUnit = rule "typeof-unit" $ fresh $ \ctx ->
      concl $ typeof ctx unit' tunit

    typeofVar = rule "typeof-var" $ fresh3 $ \ctx n ty -> do
      concl $ typeof ctx (var n) ty
      prem  $ lookupTm ctx n ty

    typeofLam = rule "typeof-lam" $ fresh4 $ \ctx tyA body tyB -> do
      concl $ typeof ctx (lam tyA body) (tarr tyA tyB)
      prem  $ typeof (tmBind tyA ctx) body tyB

    typeofApp = rule "typeof-app" $ fresh5 $ \ctx e1 e2 tyA tyB -> do
      concl $ typeof ctx (app e1 e2) tyB
      prem  $ typeof ctx e1 (tarr tyA tyB)
      prem  $ typeof ctx e2 tyA

    typeofTLam = rule "typeof-tlam" $ fresh3 $ \ctx body tyA -> do
      concl $ typeof ctx (tlam body) (tall tyA)
      prem  $ typeof (tyBind ctx) body tyA

    typeofTApp = rule "typeof-tapp" $ fresh4 $ \ctx e tyB tyA -> fresh $ \tyA' -> do
      concl $ typeof ctx (tapp e tyB) tyA'
      prem  $ typeof ctx e (tall tyA)
      prem  $ substTy zro tyB tyA tyA'

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

-- Test natLt with derivation
natLtWithTrace :: Nat -> Nat -> Stream ((), Derivation)
natLtWithTrace n m = runWithDerivationWith SystemFFormatter $ do
  appGoal $ natLt (Ground $ project n) (Ground $ project m)
  pure ()

-- Test lookupTm with derivation
lookupWithTrace :: Ctx -> Nat -> Stream (Ty, Derivation)
lookupWithTrace ctx0 n0 = runWithDerivationWith SystemFFormatter $ fresh $ \ty -> do
  appGoal $ lookupTm (Ground $ project ctx0) (Ground $ project n0) ty
  eval ty

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "=== System F Type Checking ==="
  putStrLn ""

  -- Test 1: Simple type check
  putStrLn "1. Typecheck: ()"
  print $ takeS 1 (typeofIO Nil Unit)
  putStrLn ""

  -- Test 2: Polymorphic identity
  let polyId = TLam (Lam (TVar Z) (Var Z))
  putStrLn "2. Typecheck: Λα. λx:α. x"
  print $ takeS 1 (typeofIO Nil polyId)
  putStrLn ""

  putStrLn "=== Extracted Typing Rules (DeepRedex) ==="
  putStrLn ""
  printRulesWith @'[Ctx, Tm, Ty] SystemFFormatter "typeof" typeof

  putStrLn "=== Derivation Trees (TracingRedex) ==="
  putStrLn ""

  -- Test 3: natLt derivation
  putStrLn "3. Derivation for: 0 < 2"
  case takeS 1 (natLtWithTrace Z (S (S Z))) of
    [((), deriv)] -> putStrLn $ prettyDerivation deriv
    _ -> putStrLn "No derivation found"
  putStrLn ""

  -- Test 4: natLt derivation for 1 < 3
  putStrLn "4. Derivation for: 1 < 3"
  case takeS 1 (natLtWithTrace (S Z) (S (S (S Z)))) of
    [((), deriv)] -> putStrLn $ prettyDerivation deriv
    _ -> putStrLn "No derivation found"
  putStrLn ""

  -- Test 5: lookup derivation
  let ctx1 = TmBind TUnit (TmBind (TArr TUnit TUnit) Nil)
  putStrLn "5. Derivation for: lookup (Unit, Unit→Unit, ·) 1"
  case takeS 1 (lookupWithTrace ctx1 (S Z)) of
    [(ty, deriv)] -> do
      putStrLn $ "Found type: " ++ show ty
      putStrLn $ prettyDerivation deriv
    _ -> putStrLn "No derivation found"
  putStrLn ""

  -- Test 6: Full typeof with trace
  putStrLn "6. Derivation for typeof: λx:Unit. x"
  let idUnit = Lam TUnit (Var Z)
  case takeS 1 (typeofWithTrace Nil idUnit) of
    [(ty, deriv)] -> do
      putStrLn $ "Type: " ++ show ty
      putStrLn $ prettyDerivation deriv
    _ -> putStrLn "No derivation found"
  putStrLn ""

  putStrLn "=== All examples complete ==="
