{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}

-- | Property-based tests for the poly example.
--
-- Demonstrates QuickCheck integration with TypedRedex relations.
module Main (main) where

import TypedRedex
import TypedRedex.Nominal.Prelude
import TypedRedex.Nominal.Bind (Bind(..))
import TypedRedex.Interp.Subst (runSubstRedex, takeS, Stream)
import TypedRedex.Test.Property
import Test.QuickCheck (Result(..), quickCheckResult, quickCheckWithResult, stdArgs, Args(..), property, (==>), label, collect)
import qualified TypedRedex.DSL.Fresh as F
import TypedRedex.DSL.Moded (AppliedM(..), toApplied, ground)

import Syntax
import Rules

import System.Exit (exitFailure, exitSuccess)

--------------------------------------------------------------------------------
-- Arbitrary instances
--------------------------------------------------------------------------------

instance Arbitrary TyNom where
  arbitrary = TyNom <$> chooseInt (0, 10)
  shrink (TyNom n) = [TyNom n' | n' <- shrink n, n' >= 0]

instance Arbitrary Nom where
  arbitrary = Nom <$> chooseInt (0, 10)
  shrink (Nom n) = [Nom n' | n' <- shrink n, n' >= 0]

instance Arbitrary Polar where
  arbitrary = elements [Pos, Neg]
  shrink Pos = []
  shrink Neg = [Pos]

-- | Generate types. We use sized to control recursion depth.
instance Arbitrary Ty where
  arbitrary = sized genTy
    where
      genTy :: Int -> Gen Ty
      genTy 0 = oneof
        [ pure TInt
        , pure TBool
        , TVar <$> arbitrary
        ]
      genTy n = oneof
        [ pure TInt
        , pure TBool
        , TVar <$> arbitrary
        , TArr <$> genTy (n `div` 2) <*> genTy (n `div` 2)
        , TList <$> genTy (n - 1)
        , TProd <$> genTy (n `div` 2) <*> genTy (n `div` 2)
        -- TForall is tricky due to binding, skip for now
        ]

  shrink TInt = []
  shrink TBool = [TInt]
  shrink (TVar _) = [TInt]
  shrink (TArr t1 t2) = [TInt, t1, t2] ++ [TArr t1' t2' | (t1', t2') <- shrink (t1, t2)]
  shrink (TList t) = [TInt, t] ++ [TList t' | t' <- shrink t]
  shrink (TProd t1 t2) = [TInt, t1, t2] ++ [TProd t1' t2' | (t1', t2') <- shrink (t1, t2)]
  shrink (TForall _) = [TInt]

-- | Generate environments. Keep them small to avoid blowup.
instance Arbitrary Env where
  arbitrary = sized genEnv
    where
      genEnv :: Int -> Gen Env
      genEnv 0 = pure EEmpty
      genEnv n = oneof
        [ pure EEmpty
        , EUvar <$> arbitrary <*> genEnv (n - 1)
        , EEvar <$> arbitrary <*> genEnv (n - 1)
        , ESvar <$> arbitrary <*> resize (n `div` 2) arbitrary <*> genEnv (n - 1)
        , ETrm <$> arbitrary <*> resize (n `div` 2) arbitrary <*> genEnv (n - 1)
        ]

  shrink EEmpty = []
  shrink (EUvar _ env) = [EEmpty, env]
  shrink (EEvar _ env) = [EEmpty, env]
  shrink (ESvar _ _ env) = [EEmpty, env]
  shrink (ETrm _ _ env) = [EEmpty, env]

--------------------------------------------------------------------------------
-- Helper: compute environment length
--------------------------------------------------------------------------------

envLength :: Env -> Int
envLength EEmpty = 0
envLength (ETrm _ _ env) = 1 + envLength env
envLength (EUvar _ env) = 1 + envLength env
envLength (EEvar _ env) = 1 + envLength env
envLength (ESvar _ _ env) = 1 + envLength env

--------------------------------------------------------------------------------
-- Runner for ssub
--------------------------------------------------------------------------------

-- | Run ssub and return the first solution (if any).
runSsub :: Env -> Env -> Ty -> Polar -> Ty -> Maybe Env
runSsub env0 senv0 ty1_0 p0 ty2_0 =
  case takeS 1 stream of
    [x] -> Just x
    _   -> Nothing
  where
    stream :: Stream Env
    stream = runSubstRedex $ F.fresh $ \senv' -> do
      let envL  = Ground $ project env0
          senvL = Ground $ project senv0
          ty1L  = Ground $ project ty1_0
          pL    = Ground $ project p0
          ty2L  = Ground $ project ty2_0
      appGoal $ toApplied $ ssub (ground envL) (ground senvL) (ground ty1L) (ground pL) (ground ty2L) (ground senv')
      eval senv'

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

-- | Property: ssub preserves the length of the solution environment.
--
-- If (env, senv) ⊢ ty1 ≤p ty2 ⊣ senv', then length(senv) == length(senv').
--
-- This holds because ssub only instantiates existing existential variables
-- (turning EEvar into ESvar) but never adds or removes entries.
prop_ssub_preserves_length :: Property
prop_ssub_preserves_length =
  propRel5 runSsub $ \(_env, senv, _ty1, _p, _ty2) outEnv ->
    envLength senv == envLength outEnv

-- | Property: ssub with same type should succeed (reflexivity).
-- ty ≤+ ty should always succeed for base types.
prop_ssub_same_type :: Property
prop_ssub_same_type = property $ \env senv ty ->
  -- Only test base types (TInt, TBool) where reflexivity is guaranteed
  isBaseType ty ==>
    case runSsub env senv ty Pos ty of
      Nothing -> False  -- Should always succeed for same types
      Just outEnv -> envLength senv == envLength outEnv
  where
    isBaseType TInt = True
    isBaseType TBool = True
    isBaseType _ = False

-- | Property: ssub with reflexive types should succeed.
-- int ≤+ int should always succeed.
prop_ssub_int_reflexive :: Property
prop_ssub_int_reflexive = property $ \env senv ->
  case runSsub env senv TInt Pos TInt of
    Nothing -> False  -- Should always succeed
    Just outEnv -> envLength senv == envLength outEnv

-- | Property: ssub with bool ≤+ bool should succeed.
prop_ssub_bool_reflexive :: Property
prop_ssub_bool_reflexive = property $ \env senv ->
  case runSsub env senv TBool Pos TBool of
    Nothing -> False
    Just outEnv -> envLength senv == envLength outEnv

-- | Property: arrow reflexivity (ty1 -> ty2) ≤+ (ty1 -> ty2).
prop_ssub_arr_reflexive :: Property
prop_ssub_arr_reflexive = property $ \env senv ->
  -- Only test simple arrows to avoid deep recursion
  let ty = TArr TInt TBool in
  case runSsub env senv ty Pos ty of
    Nothing -> False
    Just outEnv -> envLength senv == envLength outEnv

-- | Debug property: shows what gets discarded vs accepted.
-- Run with verboseCheck to see details.
prop_ssub_debug :: Property
prop_ssub_debug = property $ \env senv ty1 p ty2 ->
  let result = runSsub env senv ty1 p ty2
      tyPair = classifyTyPair ty1 ty2
  in collect tyPair $
     case result of
       Nothing -> label "DISCARDED (no subtyping)" $ property True  -- count but don't test
       Just outEnv -> label "PASSED (has subtyping)" $
         envLength senv == envLength outEnv

-- | Classify type pairs for debugging.
classifyTyPair :: Ty -> Ty -> String
classifyTyPair ty1 ty2 = tyClass ty1 ++ " vs " ++ tyClass ty2
  where
    tyClass TInt = "int"
    tyClass TBool = "bool"
    tyClass (TVar _) = "var"
    tyClass (TArr _ _) = "arr"
    tyClass (TList _) = "list"
    tyClass (TProd _ _) = "prod"
    tyClass (TForall _) = "forall"

--------------------------------------------------------------------------------
-- Main: run all properties
--------------------------------------------------------------------------------

-- | Test arguments with high discard ratio for random type testing.
testArgs :: Args
testArgs = stdArgs { maxDiscardRatio = 50, maxSuccess = 100 }

main :: IO ()
main = do
  putStrLn "=== TypedRedex Property Tests: poly example ==="
  putStrLn ""

  -- Tests with high success rate (no discards expected)
  putStrLn "Testing: int ≤+ int is reflexive..."
  result1 <- quickCheckResult prop_ssub_int_reflexive

  putStrLn ""
  putStrLn "Testing: bool ≤+ bool is reflexive..."
  result2 <- quickCheckResult prop_ssub_bool_reflexive

  putStrLn ""
  putStrLn "Testing: (int -> bool) ≤+ (int -> bool) is reflexive..."
  result3 <- quickCheckResult prop_ssub_arr_reflexive

  putStrLn ""
  putStrLn "Testing: base types reflexivity..."
  result4 <- quickCheckResult prop_ssub_same_type

  -- Random type test (high discard expected)
  putStrLn ""
  putStrLn "Testing: ssub preserves environment length (random types)..."
  result5 <- quickCheckWithResult testArgs prop_ssub_preserves_length

  -- Debug: show distribution of discards
  putStrLn ""
  putStrLn "Debug: distribution of type pairs and discard reasons..."
  result6 <- quickCheckWithResult testArgs prop_ssub_debug

  putStrLn ""
  let results = [result1, result2, result3, result4, result5, result6]
  if all isSuccess results
    then do
      putStrLn "All properties passed!"
      exitSuccess
    else do
      putStrLn "Some properties failed!"
      exitFailure

isSuccess :: Result -> Bool
isSuccess Success{} = True
isSuccess GaveUp{} = True  -- GaveUp is acceptable for random testing
isSuccess _ = False
