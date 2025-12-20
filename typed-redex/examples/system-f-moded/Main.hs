{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE FlexibleContexts #-}

-- | System F Type Checking with mode-checked rules.
--
-- This example demonstrates how to use the moded DSL with nominal features
-- for compile-time verification that all rules have valid execution schedules.
module Main (main) where

import TypedRedex hiding (fresh, fresh2, fresh3, fresh4, fresh5, ground, lift1, lift2, lift3)
import TypedRedex.Core.Internal.Logic (Logic (Ground), LogicType (..))
import TypedRedex.Nominal
import TypedRedex.Nominal.Prelude
import TypedRedex.Interp.Subst (runSubstRedex, takeS, Stream, RedexFresh(..))
import TypedRedex.DSL.Fresh (LTerm)
import qualified TypedRedex.DSL.Fresh as F
import qualified TypedRedex.DSL.Moded as R
import TypedRedex.DSL.Moded
  ( Mode(..), ModeList(..), T(..), TArgs(..)
  , AppliedM(..), mjudge3, toApplied, ToLTermList(..), ModedRule(..), ruleM
  , fresh, prem, concl, liftRel
  , ground, lift1, lift2, Union
  )

import Syntax

--------------------------------------------------------------------------------
-- Mode-checked lookup: lookupTm ctx x ty
-- Modes: I, I, O
--------------------------------------------------------------------------------

lookupTmM :: (RedexFresh rel, RedexEval rel)
          => T vs1 Ctx rel -> T vs2 Nom rel -> T vs3 Ty rel
          -> AppliedM rel "lookupTm" '[I, I, O] '[vs1, vs2, vs3] '[Ctx, Nom, Ty]
lookupTmM = mjudge3 (I :* I :* O :* MNil)
  [ -- lookup-here: lookupTm (x:ty, rest) x ty
    ruleM @"lookupTm" "lookup-here" $ R.do
      ty   <- fresh
      rest <- fresh
      x    <- fresh  -- logic variable for Nom (can unify with any Nom)
      R.concl $ lookupTmM (tmBindM x ty rest) x ty

  , -- lookup-there: lookupTm (y:tyY, rest) x ty ← lookupTm rest x ty
    ruleM @"lookupTm" "lookup-there" $ R.do
      x    <- fresh
      y    <- fresh  -- logic variable for Nom
      ty   <- fresh
      tyY  <- fresh
      rest <- fresh
      R.concl $ lookupTmM (tmBindM y tyY rest) x ty
      R.prem $ lookupTmM rest x ty

  , -- lookup-skip: lookupTm (alpha, rest) x ty ← lookupTm rest x ty
    ruleM @"lookupTm" "lookup-skip" $ R.do
      alpha <- fresh  -- logic variable for TyNom
      x     <- fresh
      ty    <- fresh
      rest  <- fresh
      R.concl $ lookupTmM (tyBindM alpha rest) x ty
      R.prem $ lookupTmM rest x ty
  ]

--------------------------------------------------------------------------------
-- Mode-checked typeof: typeof ctx e ty
-- Modes: I, I, O
--------------------------------------------------------------------------------

typeofM :: (RedexFresh rel, RedexEval rel)
        => T vs1 Ctx rel -> T vs2 Tm rel -> T vs3 Ty rel
        -> AppliedM rel "typeof" '[I, I, O] '[vs1, vs2, vs3] '[Ctx, Tm, Ty]
typeofM = mjudge3 (I :* I :* O :* MNil)
  [ -- typeof-unit: typeof ctx () Unit
    ruleM @"typeof" "typeof-unit" $ R.do
      ctx <- fresh
      R.concl $ typeofM ctx unitM tunitM

  , -- typeof-var: typeof ctx (Var x) ty ← lookupTm ctx x ty
    ruleM @"typeof" "typeof-var" $ R.do
      ctx <- fresh
      x   <- fresh
      ty  <- fresh
      R.concl $ typeofM ctx (varM x) ty
      R.prem $ lookupTmM ctx x ty

  , -- typeof-lam: typeof ctx (Lam tyA (bind x body)) (tyA -> tyB)
    --             ← typeof (x:tyA, ctx) body tyB
    -- Use fresh x for pattern matching, then use it in the premise
    ruleM @"typeof" "typeof-lam" $ R.do
      ctx  <- fresh
      tyA  <- fresh
      x    <- fresh  -- logic variable for the binder name
      body <- fresh
      tyB  <- fresh
      R.concl $ typeofM ctx (lamM tyA (bindNomPatM x body)) (tarrM tyA tyB)
      R.prem $ typeofM (tmBindM x tyA ctx) body tyB

  , -- typeof-app: typeof ctx (App e1 e2) tyB
    --             ← typeof ctx e1 (tyA -> tyB) ∧ typeof ctx e2 tyA
    ruleM @"typeof" "typeof-app" $ R.do
      ctx <- fresh
      e1  <- fresh
      e2  <- fresh
      tyA <- fresh
      tyB <- fresh
      R.concl $ typeofM ctx (appM e1 e2) tyB
      R.prem $ typeofM ctx e1 (tarrM tyA tyB)
      R.prem $ typeofM ctx e2 tyA

  , -- typeof-tlam: typeof ctx (TLam (bind alpha body)) (forall alpha. tyBody)
    --              ← typeof (alpha, ctx) body tyBody
    -- Use fresh alpha for pattern matching
    ruleM @"typeof" "typeof-tlam" $ R.do
      ctx    <- fresh
      alpha  <- fresh  -- logic variable for the type binder name
      body   <- fresh
      tyBody <- fresh
      R.prem $ typeofM (tyBindM alpha ctx) body tyBody
      R.concl $ typeofM ctx (tlamM (bindTyPatM alpha body)) (tallM (bindTyPatM alpha tyBody))

  , -- typeof-tapp: typeof ctx (TApp e tyArg) result
    --              ← typeof ctx e (forall. tyBnd) ∧ instantiateTo tyBnd tyArg result
    ruleM @"typeof" "typeof-tapp" $ R.do
      ctx    <- fresh
      e      <- fresh
      tyArg  <- fresh
      tyBnd  <- fresh
      result <- fresh
      R.concl $ typeofM ctx (tappM e tyArg) result
      R.prem $ typeofM ctx e (tallM tyBnd)
      -- instantiateTo is an inline operation (not a judgment)
      -- It uses tyBnd and tyArg to produce result
      liftRel $ instantiateTo (unT tyBnd) (unT tyArg) (unT result)
  ]

--------------------------------------------------------------------------------
-- Running queries
--------------------------------------------------------------------------------

typeofIO :: Ctx -> Tm -> Stream Ty
typeofIO ctx0 e0 = runSubstRedex $ F.fresh $ \ty -> do
  let ctxL = Ground $ project ctx0
      eL   = Ground $ project e0
  appGoal $ toApplied $ typeofM (T ctxL) (T eL) (T ty)
  eval ty

checkIII :: Ctx -> Tm -> Ty -> Stream ()
checkIII ctx0 e0 ty0 = runSubstRedex $ do
  let ctxL = Ground $ project ctx0
      eL   = Ground $ project e0
      tyL  = Ground $ project ty0
  appGoal $ toApplied $ typeofM (T ctxL) (T eL) (T tyL)
  pure ()

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "=== System F Type Checking (Moded) ==="
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

  putStrLn "=== Mode Checking Guarantee ==="
  putStrLn ""
  putStrLn "All rules above compile, which proves that:"
  putStrLn "  - lookupTm (I,I,O): ctx and name ground -> type output"
  putStrLn "  - typeof (I,I,O): ctx and term ground -> type output"
  putStrLn ""
  putStrLn "Key moded DSL features for nominal logic:"
  putStrLn "  - fresh: creates tracked logic variables (for pattern matching)"
  putStrLn "  - bindNomPatM/bindTyPatM: binder patterns with logic variable names"
  putStrLn "  - liftRel: lifts rel actions like instantiateTo into RuleM"
  putStrLn ""
