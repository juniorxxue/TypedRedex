{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

-- | Poly Type Inference - Print Extracted Inference Rules
module Main (main) where

import Control.Exception (catch, SomeException)

import qualified Data.Set as S
import TypedRedex (goal, inject, eval, T(..))
import TypedRedex.Logic (LogicType, Redex, RedexEval, RedexFresh, RedexNeg, RedexHash)
import TypedRedex.DSL.Fresh (fresh2)
import TypedRedex.Interp.Stream (Stream, takeS)
import TypedRedex.Interp.Tracing (TracingRedex, runTracingRedex, Derivation, prettyDerivation)
import TypedRedex.Nominal (bindT)
import TypedRedex.Nominal.Prelude (Nom(..))

import Syntax
import Rules
import Typeset

--------------------------------------------------------------------------------
-- Tracing helpers (like run2 but with derivation trees)
--------------------------------------------------------------------------------

type FullRel rel = (Redex rel, RedexEval rel, RedexFresh rel, RedexNeg rel, RedexHash rel)

-- | Run a judgment with 2 outputs, returning results with derivation trees.
--
-- @
-- trace2 $ \\ty env -> goal $ infer eempty cempty (lit 1) ty env
-- @
trace2 :: (LogicType a, LogicType b)
       => (forall s. FullRel (TracingRedex s) => T '[] a (TracingRedex s) -> T '[] b (TracingRedex s) -> TracingRedex s ())
       -> Stream ((a, b), Derivation)
trace2 f = runTracingRedex $ fresh2 $ \x y -> do
  f (T S.empty x) (T S.empty y)
  (,) <$> eval x <*> eval y

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

-- | Try to print rules, handling exceptions gracefully
tryTypeset :: String -> IO () -> IO ()
tryTypeset name action = do
  putStrLn $ "--- " ++ name ++ " ---\n"
  action `catch` \(e :: SomeException) ->
    putStrLn $ "(some rules could not be typeset: " ++ take 50 (show e) ++ "...)\n"

main :: IO ()
main = do
  putStrLn "=== Quick Test with Tracing Interpreter ==="
  putStrLn ""

  -- Test 1: Literal
  putStrLn "Test 1: infer eempty cempty (lit 1)"
  let results1 = trace2 $ \ty env -> goal $ infer eempty cempty (lit (inject (1 :: Int))) ty env
  case takeS (1 :: Int) results1 of
    [] -> putStrLn "  No results!"
    ((ty, _), deriv):_ -> do
      putStrLn $ "  => Type: " ++ show ty
      putStrLn "  => Derivation:"
      putStrLn $ prettyDerivation deriv

  -- Test 2: Annotated identity (λx.x : int→int)
  putStrLn "\nTest 2: infer eempty cempty (ann (lam x.x) (int→int))"
  let results2 = trace2 $ \ty env ->
        let x = inject (Nom 0)
        in goal $ infer eempty cempty (ann (lam (bindT x (var x))) (tarr tint tint)) ty env
  case takeS (1 :: Int) results2 of
    [] -> putStrLn "  No results!"
    ((ty, _), deriv):_ -> do
      putStrLn $ "  => Type: " ++ show ty
      putStrLn "  => Derivation:"
      putStrLn $ prettyDerivation deriv

  -- Test 3: Application ((λx.x : int→int) 1)
  putStrLn "\nTest 3: infer eempty cempty (app (ann (lam x.x) (int→int)) 1)"
  let results3 = trace2 $ \ty env ->
        let x = inject (Nom 0)
        in goal $ infer eempty cempty (app (ann (lam (bindT x (var x))) (tarr tint tint)) (lit (inject (1 :: Int)))) ty env
  case takeS (1 :: Int) results3 of
    [] -> putStrLn "  No results!"
    ((ty, _), deriv):_ -> do
      putStrLn $ "  => Type: " ++ show ty
      putStrLn "  => Derivation:"
      putStrLn $ prettyDerivation deriv

  -- Test 4: Unannotated application ((λx.x) 1) - this was the original test2
  putStrLn "\nTest 4: infer eempty cempty (app (lam x.x) 1)"
  let results4 = trace2 $ \ty env ->
        let x = inject (Nom 0)
        in goal $ infer eempty cempty (app (lam (bindT x (var x))) (lit (inject (1 :: Int)))) ty env
  case takeS (1 :: Int) results4 of
    [] -> putStrLn "  No results!"
    ((ty, _), deriv):_ -> do
      putStrLn $ "  => Type: " ++ show ty
      putStrLn "  => Derivation:"
      putStrLn $ prettyDerivation deriv

  -- putStrLn ""
  -- putStrLn "=== Extracted Inference Rules for Poly ===\n"

  -- tryTypeset "flipPolar"      $ typeset2 flipPolar
  -- tryTypeset "lookupTmVar"    $ typeset3 lookupTmVar
  -- tryTypeset "lookupUvar"     $ typeset2 lookupUvar
  -- tryTypeset "lookupBoundVar" $ typeset4 lookupBoundVar
  -- tryTypeset "glb"            $ typeset3 glb
  -- tryTypeset "lub"            $ typeset3 lub
  -- tryTypeset "updateUpper"    $ typeset4 updateUpper
  -- tryTypeset "updateLower"    $ typeset4 updateLower
  -- tryTypeset "inst"           $ typeset5 inst
  -- tryTypeset "instP"          $ typeset6 instP
  -- tryTypeset "ssub"           $ typeset5 ssub
  -- tryTypeset "sub"            $ typeset5 sub
  tryTypeset "infer"          $ typeset5 infer
