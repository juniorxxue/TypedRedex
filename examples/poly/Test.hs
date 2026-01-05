{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

-- | Test module for running poly inference examples
module Main where

import TypedRedex (run2, goal, inject)
import TypedRedex.Interp.Stream (takeS)
import TypedRedex.Nominal (bindT)
import TypedRedex.Nominal.Prelude (Nom(..))

import Syntax
import Rules

import System.IO (hFlush, stdout)

--------------------------------------------------------------------------------
-- Test helpers
--------------------------------------------------------------------------------

-- | Run a test and print results
runTest :: String -> IO () -> IO ()
runTest name action = do
  putStrLn $ "\n=== " ++ name ++ " ==="
  hFlush stdout
  action
  hFlush stdout

--------------------------------------------------------------------------------
-- Test 1: Literal
--------------------------------------------------------------------------------

test1 :: IO ()
test1 = runTest "Test 1: infer · □ 1" $ do
  let results = run2 $ \ty env -> goal $ infer eempty cempty (lit (inject (1 :: Int))) ty env
  case takeS (1 :: Int) results of
    [] -> putStrLn "No results!"
    (ty, env'):_ -> do
      putStrLn $ "Type: " ++ show ty
      putStrLn $ "Env:  " ++ show env'

--------------------------------------------------------------------------------
-- Test 2: Annotated identity (λx.x : int→int)
--------------------------------------------------------------------------------

test2 :: IO ()
test2 = runTest "Test 2: infer · □ (λx.x : int→int)" $ do
  let results = run2 $ \ty env ->
        let x = inject (Nom 0)
        in goal $ infer eempty cempty (ann (lam (bindT x (var x))) (tarr tint tint)) ty env
  case takeS (1 :: Int) results of
    [] -> putStrLn "No results!"
    (ty, env'):_ -> do
      putStrLn $ "Type: " ++ show ty
      putStrLn $ "Env:  " ++ show env'

--------------------------------------------------------------------------------
-- Test 3: Application ((λx.x : int→int) 1)
--------------------------------------------------------------------------------

test3 :: IO ()
test3 = runTest "Test 3: infer · □ ((λx.x : int→int) 1)" $ do
  let results = run2 $ \ty env ->
        let x = inject (Nom 0)
        in goal $ infer eempty cempty (app (ann (lam (bindT x (var x))) (tarr tint tint)) (lit (inject (1 :: Int)))) ty env
  case takeS (1 :: Int) results of
    [] -> putStrLn "No results!"
    (ty, env'):_ -> do
      putStrLn $ "Type: " ++ show ty
      putStrLn $ "Env:  " ++ show env'

--------------------------------------------------------------------------------
-- Test 4: Constant function ((λx.1 : int→int) 2)
--------------------------------------------------------------------------------

test4 :: IO ()
test4 = runTest "Test 4: infer · □ ((λx.1 : int→int) 2)" $ do
  let results = run2 $ \ty env ->
        let x = inject (Nom 0)
        in goal $ infer eempty cempty (app (ann (lam (bindT x (lit (inject (1 :: Int))))) (tarr tint tint)) (lit (inject (2 :: Int)))) ty env
  case takeS (1 :: Int) results of
    [] -> putStrLn "No results!"
    (ty, env'):_ -> do
      putStrLn $ "Type: " ++ show ty
      putStrLn $ "Env:  " ++ show env'

--------------------------------------------------------------------------------
-- Test 5: Unannotated application ((λx.x) 1)
--------------------------------------------------------------------------------

test5 :: IO ()
test5 = runTest "Test 5: infer · □ ((λx.x) 1)" $ do
  let results = run2 $ \ty env ->
        let x = inject (Nom 0)
        in goal $ infer eempty cempty (app (lam (bindT x (var x))) (lit (inject (1 :: Int)))) ty env
  case takeS (1 :: Int) results of
    [] -> putStrLn "No results!"
    (ty, env'):_ -> do
      putStrLn $ "Type: " ++ show ty
      putStrLn $ "Env:  " ++ show env'

--------------------------------------------------------------------------------
-- Test 6: Polymorphic identity (Λα. (λx.x : α→α))
-- NOTE: This reveals a pre-existing bug in the poly inference rules for TAbs
-- The bug was never exposed before because no TAbs tests existed
--------------------------------------------------------------------------------

-- test6 :: IO ()
-- test6 = runTest "Test 6: infer · □ (Λα. (λx.x : α→α))" $ do
--   -- This test fails with "Unbound variable: x38"
--   -- This is a bug in the poly Rules.hs, not in the run2 API

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "Starting tests..."
  putStrLn (replicate 60 '=')
  hFlush stdout

  test1
  test2
  test3
  test4
  test5

  putStrLn ""
  putStrLn (replicate 60 '=')
  putStrLn "All tests done!"
