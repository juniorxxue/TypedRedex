{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

-- | Test module for running poly inference examples
module Main where

import TypedRedex hiding (ground)
import TypedRedex.Interp.Tracing (runTracingRedex, prettyDerivation, Derivation, TracingRedex)
import TypedRedex.Interp.Subst (runSubstRedex)
import TypedRedex.Interp.Stream (Stream(..), takeS)
import TypedRedex.DSL.Moded (T(..), ground)
import TypedRedex.Nominal (bindT)
import TypedRedex.Nominal.Prelude (Nom(..))

import Syntax
import Rules

import qualified Data.Set as S
import System.IO (hFlush, stdout)

--------------------------------------------------------------------------------
-- Smart constructor for ground Int
--------------------------------------------------------------------------------

-- | Create a ground integer term
gint :: Int -> T '[] Int rel
gint n = ground (Ground (project n))

-- | Create a ground Nom term
gnom :: Nom -> T '[] Nom rel
gnom n = ground (Ground (project n))

--------------------------------------------------------------------------------
-- Test 1: infer · □ 1 (using fast SubstRedex)
--------------------------------------------------------------------------------

test1 :: IO ()
test1 = do
  putStrLn "=== Test 1: infer · □ 1 ==="
  hFlush stdout
  putStrLn "Input: infer eempty cempty (lit 1)"
  hFlush stdout
  putStrLn ""

  let results :: Stream (Ty, Env)
      results = runSubstRedex $ do
        fresh2 $ \ty env' -> do
          let applied = toApplied $
                infer eempty cempty (lit (gint 1)) (T S.empty ty) (T S.empty env')
          appGoal applied
          tyVal <- eval ty
          envVal <- eval env'
          return (tyVal, envVal)

  putStrLn "Taking first result..."
  hFlush stdout
  case takeS (1 :: Int) results of
    [] -> putStrLn "No results!"
    (ty, env'):_ -> do
      putStrLn $ "Output type: " ++ show ty
      putStrLn $ "Output env:  " ++ show env'
  hFlush stdout

--------------------------------------------------------------------------------
-- Test 1 with derivation tree
--------------------------------------------------------------------------------

test1Trace :: IO ()
test1Trace = do
  putStrLn "\n=== Test 1 with derivation tree ==="
  hFlush stdout
  putStrLn ""

  let results :: Stream ((Ty, Env), Derivation)
      results = runTracingRedex $ do
        fresh2 $ \(ty :: LTerm Ty (TracingRedex s)) (env' :: LTerm Env (TracingRedex s)) -> do
          let applied = toApplied $
                infer eempty cempty (lit (gint 1)) (T S.empty ty) (T S.empty env')
          appGoal applied
          tyVal <- eval ty
          envVal <- eval env'
          return (tyVal, envVal)

  putStrLn "Taking first result with derivation..."
  hFlush stdout
  case takeS (1 :: Int) results of
    [] -> putStrLn "No results!"
    ((ty, env'), deriv):_ -> do
      putStrLn $ "Output type: " ++ show ty
      putStrLn $ "Output env:  " ++ show env'
      putStrLn ""
      putStrLn "Derivation:"
      putStrLn $ prettyDerivation deriv
  hFlush stdout

--------------------------------------------------------------------------------
-- Test 1b: infer · □ (λx.x : int→int) - simpler test with annotation
--------------------------------------------------------------------------------

test1b :: IO ()
test1b = do
  putStrLn "\n=== Test 1b: infer · □ (λx.x : int→int) ==="
  hFlush stdout
  putStrLn "Input: infer eempty cempty (ann (lam x. var x) (int->int))"
  hFlush stdout
  putStrLn ""

  let results :: Stream (Ty, Env)
      results = runSubstRedex $ do
        fresh2 $ \ty env' -> do
          let x :: Nom
              x = Nom 0
              identity = lam (bindT (gnom x) (var (gnom x)))
              intToInt = tarr tint tint
              term = ann identity intToInt
          let applied = toApplied $
                infer eempty cempty term (T S.empty ty) (T S.empty env')
          appGoal applied
          tyVal <- eval ty
          envVal <- eval env'
          return (tyVal, envVal)

  putStrLn "Taking first result..."
  hFlush stdout
  case takeS (1 :: Int) results of
    [] -> putStrLn "No results!"
    (ty, env'):_ -> do
      putStrLn $ "Output type: " ++ show ty
      putStrLn $ "Output env:  " ++ show env'
  hFlush stdout

test1bTrace :: IO ()
test1bTrace = do
  putStrLn "\n=== Test 1b with derivation tree ==="
  hFlush stdout
  putStrLn ""

  let results :: Stream ((Ty, Env), Derivation)
      results = runTracingRedex $ do
        fresh2 $ \(ty :: LTerm Ty (TracingRedex s)) (env' :: LTerm Env (TracingRedex s)) -> do
          let x :: Nom
              x = Nom 0
              identity :: T '[] Tm (TracingRedex s)
              identity = lam (bindT (gnom x) (var (gnom x)))
              intToInt :: T '[] Ty (TracingRedex s)
              intToInt = tarr tint tint
              term :: T '[] Tm (TracingRedex s)
              term = ann identity intToInt
          let applied = toApplied $
                infer eempty cempty term (T S.empty ty) (T S.empty env')
          appGoal applied
          tyVal <- eval ty
          envVal <- eval env'
          return (tyVal, envVal)

  putStrLn "Taking first result with derivation..."
  hFlush stdout
  case takeS (1 :: Int) results of
    [] -> putStrLn "No results!"
    ((ty, env'), deriv):_ -> do
      putStrLn $ "Output type: " ++ show ty
      putStrLn $ "Output env:  " ++ show env'
      putStrLn ""
      putStrLn "Derivation:"
      putStrLn $ prettyDerivation deriv
  hFlush stdout

--------------------------------------------------------------------------------
-- Test 1c: infer · □ ((λx.1 : int→int) 2) - simpler app with annotated lambda
--------------------------------------------------------------------------------

test1c :: IO ()
test1c = do
  putStrLn "\n=== Test 1c: infer · □ ((λx.1 : int→int) 2) ==="
  hFlush stdout
  putStrLn "Testing with TracingRedex instead..."
  hFlush stdout
  putStrLn ""

  let results :: Stream ((Ty, Env), Derivation)
      results = runTracingRedex $ do
        fresh2 $ \(ty :: LTerm Ty (TracingRedex s)) (env' :: LTerm Env (TracingRedex s)) -> do
          let x :: Nom
              x = Nom 0
              constOne :: T '[] Tm (TracingRedex s)
              constOne = lam (bindT (gnom x) (lit (gint 1)))
              intToInt :: T '[] Ty (TracingRedex s)
              intToInt = tarr tint tint
              annotatedConst :: T '[] Tm (TracingRedex s)
              annotatedConst = ann constOne intToInt
              two :: T '[] Tm (TracingRedex s)
              two = lit (gint 2)
              term :: T '[] Tm (TracingRedex s)
              term = app annotatedConst two
          let applied = toApplied $
                infer eempty cempty term (T S.empty ty) (T S.empty env')
          appGoal applied
          tyVal <- eval ty
          envVal <- eval env'
          return (tyVal, envVal)

  putStrLn "Taking first result with derivation..."
  hFlush stdout
  case takeS (1 :: Int) results of
    [] -> putStrLn "No results!"
    ((ty, env'), deriv):_ -> do
      putStrLn $ "Output type: " ++ show ty
      putStrLn $ "Output env:  " ++ show env'
      putStrLn ""
      putStrLn "Derivation:"
      putStrLn $ prettyDerivation deriv
  hFlush stdout

test1cTrace :: IO ()
test1cTrace = do
  putStrLn "\n=== Test 1c with derivation tree ==="
  hFlush stdout
  putStrLn ""

  let results :: Stream ((Ty, Env), Derivation)
      results = runTracingRedex $ do
        fresh2 $ \(ty :: LTerm Ty (TracingRedex s)) (env' :: LTerm Env (TracingRedex s)) -> do
          let x :: Nom
              x = Nom 0
              constOne :: T '[] Tm (TracingRedex s)
              constOne = lam (bindT (gnom x) (lit (gint 1)))
              intToInt :: T '[] Ty (TracingRedex s)
              intToInt = tarr tint tint
              annotatedConst :: T '[] Tm (TracingRedex s)
              annotatedConst = ann constOne intToInt
              two :: T '[] Tm (TracingRedex s)
              two = lit (gint 2)
              term :: T '[] Tm (TracingRedex s)
              term = app annotatedConst two
          let applied = toApplied $
                infer eempty cempty term (T S.empty ty) (T S.empty env')
          appGoal applied
          tyVal <- eval ty
          envVal <- eval env'
          return (tyVal, envVal)

  putStrLn "Taking first result with derivation..."
  hFlush stdout
  case takeS (1 :: Int) results of
    [] -> putStrLn "No results!"
    ((ty, env'), deriv):_ -> do
      putStrLn $ "Output type: " ++ show ty
      putStrLn $ "Output env:  " ++ show env'
      putStrLn ""
      putStrLn "Derivation:"
      putStrLn $ prettyDerivation deriv
  hFlush stdout

--------------------------------------------------------------------------------
-- Test 2: infer · □ ((λx. x) 1)
--------------------------------------------------------------------------------

test2 :: IO ()
test2 = do
  putStrLn "\n=== Test 2: infer · □ ((λx. x) 1) ==="
  hFlush stdout
  putStrLn "Input: infer eempty cempty (app (lam x. var x) (lit 1))"
  hFlush stdout
  putStrLn ""

  let results :: Stream (Ty, Env)
      results = runSubstRedex $ do
        fresh2 $ \ty env' -> do
          let x :: Nom
              x = Nom 0
              identity = lam (bindT (gnom x) (var (gnom x)))
              one = lit (gint 1)
              term = app identity one
          let applied = toApplied $
                infer eempty cempty term (T S.empty ty) (T S.empty env')
          appGoal applied
          tyVal <- eval ty
          envVal <- eval env'
          return (tyVal, envVal)

  putStrLn "Taking first result..."
  hFlush stdout
  case takeS (1 :: Int) results of
    [] -> putStrLn "No results!"
    (ty, env'):_ -> do
      putStrLn $ "Output type: " ++ show ty
      putStrLn $ "Output env:  " ++ show env'
  hFlush stdout

--------------------------------------------------------------------------------
-- Test 2 with derivation tree
--------------------------------------------------------------------------------

test2Trace :: IO ()
test2Trace = do
  putStrLn "\n=== Test 2 with derivation tree ==="
  hFlush stdout
  putStrLn ""

  let results :: Stream ((Ty, Env), Derivation)
      results = runTracingRedex $ do
        fresh2 $ \(ty :: LTerm Ty (TracingRedex s)) (env' :: LTerm Env (TracingRedex s)) -> do
          let x :: Nom
              x = Nom 0
              identity :: T '[] Tm (TracingRedex s)
              identity = lam (bindT (gnom x) (var (gnom x)))
              one :: T '[] Tm (TracingRedex s)
              one = lit (gint 1)
              term :: T '[] Tm (TracingRedex s)
              term = app identity one
          let applied = toApplied $
                infer eempty cempty term (T S.empty ty) (T S.empty env')
          appGoal applied
          tyVal <- eval ty
          envVal <- eval env'
          return (tyVal, envVal)

  putStrLn "Taking first result with derivation..."
  hFlush stdout
  case takeS (1 :: Int) results of
    [] -> putStrLn "No results!"
    ((ty, env'), deriv):_ -> do
      putStrLn $ "Output type: " ++ show ty
      putStrLn $ "Output env:  " ++ show env'
      putStrLn ""
      putStrLn "Derivation:"
      putStrLn $ prettyDerivation deriv
  hFlush stdout

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "Starting tests..."
  hFlush stdout

  test1
  test1Trace

  putStrLn ""
  putStrLn (replicate 60 '=')
  hFlush stdout

  test1b
  test1bTrace

  putStrLn ""
  putStrLn (replicate 60 '=')
  hFlush stdout

  test1c
  -- Skip trace for now
  -- test1cTrace

  putStrLn "\nAll tests done!"
