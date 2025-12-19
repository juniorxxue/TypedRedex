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

  putStrLn "=== Alpha-Equivalence Tests ==="
  putStrLn ""

  -- Test 9: Alpha-equivalence of term binders
  -- λx:Unit. x  should equal  λy:Unit. y
  let x100 = Nom 100
      y200 = Nom 200
      lamX = Lam TUnit (Bind x100 (Var x100))  -- λx. x
      lamY = Lam TUnit (Bind y200 (Var y200))  -- λy. y
  putStrLn "9. Alpha-equivalence: (λx:Unit. x) =α= (λy:Unit. y)"
  putStrLn $ "   lamX = " ++ show lamX
  putStrLn $ "   lamY = " ++ show lamY
  let alphaTest1 = runSubstRedex $ do
        (Ground (project lamX)) <=> (Ground (project lamY))
        pure "unified!"
  putStrLn $ "   Result: " ++ show (takeS 1 alphaTest1)
  putStrLn ""

  -- Test 10: Alpha-equivalence of type binders
  -- ∀α. α  should equal  ∀β. β
  let alpha100 = TyNom 100
      beta200 = TyNom 200
      forallAlpha = TAll (Bind alpha100 (TVar alpha100))  -- ∀α. α
      forallBeta  = TAll (Bind beta200 (TVar beta200))    -- ∀β. β
  putStrLn "10. Alpha-equivalence: (∀α. α) =α= (∀β. β)"
  putStrLn $ "    forallAlpha = " ++ show forallAlpha
  putStrLn $ "    forallBeta  = " ++ show forallBeta
  let alphaTest2 = runSubstRedex $ do
        (Ground (project forallAlpha)) <=> (Ground (project forallBeta))
        pure "unified!"
  putStrLn $ "    Result: " ++ show (takeS 1 alphaTest2)
  putStrLn ""

  -- Test 11: Alpha-equivalence with more complex bodies
  -- ∀α. α → α  should equal  ∀β. β → β
  let forallArr1 = TAll (Bind alpha100 (TArr (TVar alpha100) (TVar alpha100)))
      forallArr2 = TAll (Bind beta200 (TArr (TVar beta200) (TVar beta200)))
  putStrLn "11. Alpha-equivalence: (∀α. α→α) =α= (∀β. β→β)"
  let alphaTest3 = runSubstRedex $ do
        (Ground (project forallArr1)) <=> (Ground (project forallArr2))
        pure "unified!"
  putStrLn $ "    Result: " ++ show (takeS 1 alphaTest3)
  putStrLn ""

  -- Test 12: NON-alpha-equivalent types should NOT unify
  -- ∀α. α  should NOT equal  ∀α. Unit
  let forallUnit = TAll (Bind alpha100 TUnit)
  putStrLn "12. Non-equivalence: (∀α. α) ≠ (∀α. Unit)"
  let alphaTest4 = runSubstRedex $ do
        (Ground (project forallAlpha)) <=> (Ground (project forallUnit))
        pure "unified!"
  putStrLn $ "    Result (should be empty): " ++ show (takeS 1 alphaTest4)
  putStrLn ""

  putStrLn "=== Substitution Tests ==="
  putStrLn ""

  -- Test 13: Simple substitution (no capture)
  -- [Unit/α](α → α) = Unit → Unit
  let tyBody = TArr (TVar alpha100) (TVar alpha100)  -- α → α
      substResult1 = subst alpha100 TUnit tyBody
  putStrLn "13. Substitution: [Unit/α](α → α)"
  putStrLn $ "    Before: " ++ show tyBody
  putStrLn $ "    After:  " ++ show substResult1
  putStrLn $ "    Expected: Unit → Unit"
  putStrLn ""

  -- Test 14: Substitution with shadowing (should NOT substitute under shadow)
  -- [Unit/α](∀α. α) = ∀α. α  (α is shadowed)
  let substResult2 = subst alpha100 TUnit forallAlpha
  putStrLn "14. Substitution with shadowing: [Unit/α](∀α. α)"
  putStrLn $ "    Before: " ++ show forallAlpha
  putStrLn $ "    After:  " ++ show substResult2
  putStrLn $ "    Expected: ∀α. α (unchanged, shadowed)"
  putStrLn ""

  -- Test 15: Substitution under binder (no capture risk)
  -- [Unit/α](∀β. α → β) = ∀β. Unit → β
  let gamma300 = TyNom 300
      forallGammaAlpha = TAll (Bind gamma300 (TArr (TVar alpha100) (TVar gamma300)))
      substResult3 = subst alpha100 TUnit forallGammaAlpha
  putStrLn "15. Substitution under binder: [Unit/α](∀γ. α → γ)"
  putStrLn $ "    Before: " ++ show forallGammaAlpha
  putStrLn $ "    After:  " ++ show substResult3
  putStrLn $ "    Expected: ∀γ. Unit → γ"
  putStrLn ""

  -- Test 16: CAPTURE TEST - This is where naive substitution fails!
  -- [β/α](∀β. α → β) should be ∀β'. β → β' (with fresh β')
  -- But naive substitution gives ∀β. β → β (WRONG - β is captured!)
  let forallBetaAlpha = TAll (Bind beta200 (TArr (TVar alpha100) (TVar beta200)))
      -- Substituting β for α
      substResult4 = subst alpha100 (TVar beta200) forallBetaAlpha
  putStrLn "16. CAPTURE TEST: [β/α](∀β. α → β)"
  putStrLn $ "    Before: " ++ show forallBetaAlpha
  putStrLn $ "    After:  " ++ show substResult4
  putStrLn $ "    Expected (capture-avoiding): ∀β'. β → β' (fresh β')"
  putStrLn $ "    Actual (naive, WRONG if captured): ∀β. β → β"
  -- Check if capture occurred
  case substResult4 of
    TAll (Bind boundVar (TArr t1 t2)) ->
      if t1 == TVar boundVar
        then putStrLn "    WARNING: Capture occurred! The free β became bound."
        else putStrLn "    OK: No capture (or properly renamed)."
    _ -> putStrLn "    Unexpected result shape"
  putStrLn ""

  -- Test 17: Type application that exercises substitution
  -- (Λα. λx:α. x) [∀β. β]  should typecheck
  -- Result type: (∀β. β) → (∀β. β)
  let polyType = TAll (Bind beta200 (TVar beta200))  -- ∀β. β
      polyIdWithPolyArg = TApp polyId polyType
  putStrLn "17. Typecheck: (Λα. λx:α. x) [∀β. β]"
  putStrLn $ "    Expected type: (∀β. β) → (∀β. β)"
  print $ takeS 1 (typeofIO Nil polyIdWithPolyArg)
  putStrLn ""

  putStrLn "=== Hash Constraint Tests ==="
  putStrLn ""

  -- Test 18: Demonstrate hash constraint for capture avoidance
  -- The hash constraint α # β asserts α ≠ β (α does not occur in β)
  putStrLn "18. Hash constraint: α # β (α does not occur free in β)"
  let hashTest1 = runSubstRedex $ do
        -- α # β should succeed when α ≠ β
        hash (tynom alpha100) (tynom beta200)
        pure "α # β succeeded (they're different)"
  putStrLn $ "    hash α100 β200: " ++ show (takeS 1 hashTest1)

  let hashTest2 = runSubstRedex $ do
        -- α # α should fail (α occurs in α)
        hash (tynom alpha100) (tynom alpha100)
        pure "α # α succeeded (BUG!)"
  putStrLn $ "    hash α100 α100: " ++ show (takeS 1 hashTest2) ++ " (should be empty)"
  putStrLn ""

  -- Test 19: Hash in types - α # (β → β)
  putStrLn "19. Hash in types: α # (β → β)"
  let tyBetaArr = TArr (TVar beta200) (TVar beta200)  -- β → β
  let hashTest3 = runSubstRedex $ do
        hash (tynom alpha100) (Ground (project tyBetaArr))
        pure "α # (β → β) succeeded"
  putStrLn $ "    hash α (β → β): " ++ show (takeS 1 hashTest3)

  let tyAlphaArr = TArr (TVar alpha100) (TVar alpha100)  -- α → α
  let hashTest4 = runSubstRedex $ do
        hash (tynom alpha100) (Ground (project tyAlphaArr))
        pure "α # (α → α) succeeded (BUG!)"
  putStrLn $ "    hash α (α → α): " ++ show (takeS 1 hashTest4) ++ " (should be empty)"
  putStrLn ""

  -- Test 20: Hash with binder - α # (∀α. α) should succeed (α is bound)
  putStrLn "20. Hash with shadowing: α # (∀α. α)"
  let hashTest5 = runSubstRedex $ do
        hash (tynom alpha100) (Ground (project forallAlpha))
        pure "α # (∀α. α) succeeded (α is shadowed)"
  putStrLn $ "    hash α100 (∀α100. α100): " ++ show (takeS 1 hashTest5)
  putStrLn ""

  -- Test 21: Using hash for capture-avoiding substitution
  -- To properly do [β/α](∀β. α → β), we need:
  -- 1. Pick fresh γ where γ # β (the replacement)
  -- 2. Rename ∀β to ∀γ
  -- 3. Then substitute
  putStrLn "21. Capture-avoiding substitution via hash + swap:"
  putStrLn "    [β/α](∀β. α → β) with fresh γ where γ # β"
  let captureAvoidTest = runSubstRedex $ do
        -- Pick a fresh name
        gamma <- freshTyNom
        -- Ensure gamma # replacement (β)
        hash (tynom gamma) (tvar (tynom beta200))
        -- Now gamma is safe to use as binder
        -- Original: ∀β. α → β  (with β = beta200, α = alpha100)
        -- After renaming β to γ: ∀γ. α → γ
        -- After substituting [β/α]: ∀γ. β → γ
        let renamedBody = TArr (TVar alpha100) (TVar gamma)  -- α → γ (after swap)
        let result = TAll (Bind gamma (subst alpha100 (TVar beta200) renamedBody))
        pure result
  case takeS 1 captureAvoidTest of
    [result] -> do
      putStrLn $ "    Result: " ++ show result
      case result of
        TAll (Bind boundVar (TArr t1 t2)) ->
          if t1 == TVar beta200 && t2 == TVar boundVar && boundVar /= beta200
            then putStrLn "    CORRECT: ∀γ. β → γ (no capture!)"
            else putStrLn "    Check the result structure"
        _ -> putStrLn "    Unexpected shape"
    [] -> putStrLn "    No result (constraint failed)"
  putStrLn ""

  putStrLn "=== All tests completed ==="
