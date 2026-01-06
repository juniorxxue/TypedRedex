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
import TypedRedex.DSL.Fresh (fresh, fresh2)
import TypedRedex.Interp.Stream (Stream, takeS)
import TypedRedex.Interp.Tracing (TracingRedex, runTracingRedex, Derivation, prettyDerivation)
import TypedRedex.Interp.Tracing.Deterministic (TracingRedexDet, TraceOutcome(..), runTracingRedexDet)
import TypedRedex.Nominal (bindT)
import TypedRedex.Nominal.Prelude (Nom(..), TyNom(..))

import Syntax
import Rules
import Typeset
import Syntax (eempty)

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

-- | Run a judgment with 1 output, returning results with derivation trees.
trace1 :: LogicType a
       => (forall s. FullRel (TracingRedex s) => T '[] a (TracingRedex s) -> TracingRedex s ())
       -> Stream (a, Derivation)
trace1 f = runTracingRedex $ fresh $ \x -> do
  f (T S.empty x)
  eval x

--------------------------------------------------------------------------------
-- Deterministic failure tracing (for partial derivations on failed examples)
--------------------------------------------------------------------------------

-- | Like trace1, but returns either a success derivation or a partial failure tree.
trace1Det :: LogicType a
          => (forall s. FullRel (TracingRedexDet s) => T '[] a (TracingRedexDet s) -> TracingRedexDet s ())
          -> TraceOutcome a
trace1Det f = runTracingRedexDet $ fresh $ \x -> do
  f (T S.empty x)
  eval x

-- | Run a goal (no outputs) and still get either a success derivation or a
-- partial failure tree. Useful when the goal itself is the thing you're
-- debugging, and evaluating outputs isn't necessary.
trace0Det :: (forall s. FullRel (TracingRedexDet s) => TracingRedexDet s ())
          -> TraceOutcome ()
trace0Det = runTracingRedexDet

runTestDet :: Show a => String -> TraceOutcome a -> IO ()
runTestDet name outcome = do
  putStrLn $ "\n" ++ name
  case outcome of
    TraceSuccess result deriv -> do
      putStrLn $ "  => Result: " ++ show result
      putStrLn "  => Derivation:"
      putStrLn $ prettyDerivation deriv
    TraceFailure deriv -> do
      putStrLn "  No results."
      putStrLn "  => Partial derivation:"
      putStrLn $ prettyDerivation deriv

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

-- | Try to print rules, handling exceptions gracefully
tryTypeset :: String -> IO () -> IO ()
tryTypeset name action = do
  putStrLn $ "--- " ++ name ++ " ---\n"
  action `catch` \(e :: SomeException) ->
    putStrLn $ "(some rules could not be typeset: " ++ take 50 (show e) ++ "...)\n"

-- | Run an inference test and print results
runTest :: Show a => String -> Stream ((a, b), Derivation) -> IO ()
runTest name results = do
  putStrLn $ "\n" ++ name
  case takeS (1 :: Int) results of
    [] -> putStrLn "  No results!"
    ((ty, _), deriv):_ -> do
      putStrLn $ "  => Type: " ++ show ty
      putStrLn "  => Derivation:"
      putStrLn $ prettyDerivation deriv

-- | Run a test with 1 output and print results
runTest1 :: Show a => String -> Stream (a, Derivation) -> IO ()
runTest1 name results = do
  putStrLn $ "\n" ++ name
  case takeS (1 :: Int) results of
    [] -> putStrLn "  No results!"
    (result, deriv):_ -> do
      putStrLn $ "  => Result: " ++ show result
      putStrLn "  => Derivation:"
      putStrLn $ prettyDerivation deriv

main :: IO ()
main = do
  tryTypeset "ssub"           $ typeset5 ssub
  tryTypeset "sub"            $ typeset5 sub
  tryTypeset "infer"          $ typeset5 infer

  putStrLn "=== Quick Test with Tracing Interpreter ==="

  -- Test 1: Literal
  runTest "Test 1: infer eempty cempty (lit 1)" $
    trace2 $ \ty env -> goal $ infer eempty cempty (lit (inject (1 :: Int))) ty env

  -- Test 2: Annotated identity (λx.x : int→int)
  runTest "Test 2: infer eempty cempty (ann (lam x.x) (int→int))" $
    trace2 $ \ty env ->
      let x = inject (Nom 0)
      in goal $ infer eempty cempty (ann (lam (bindT x (var x))) (tarr tint tint)) ty env

  -- Test 3: Application ((λx.x : int→int) 1)
  runTest "Test 3: infer eempty cempty (app (ann (lam x.x) (int→int)) 1)" $
    trace2 $ \ty env ->
      let x = inject (Nom 0)
      in goal $ infer eempty cempty (app (ann (lam (bindT x (var x))) (tarr tint tint)) (lit (inject (1 :: Int)))) ty env

  -- Test 4: Unannotated application ((λx.x) 1)
  runTest "Test 4: infer eempty cempty (app (lam x.x) 1)" $
    trace2 $ \ty env ->
      let x = inject (Nom 0)
      in goal $ infer eempty cempty (app (lam (bindT x (var x))) (lit (inject (1 :: Int)))) ty env

  -- Test 5: Polymorphic identity: id = /\a. (\x. x : a -> a)
  -- runTest "Test 5: infer eempty cempty (/\\a. (\\x. x : a -> a))" $
  --   trace2 $ \ty env ->
  --     let a = inject (TyNom 0)
  --         x = inject (Nom 1)
  --     in goal $ infer eempty cempty
  --          (tlam (bindT a (ann (lam (bindT x (var x))) (tarr (tvar a) (tvar a)))))
  --          ty env

  -- -- Test 6: id applied to 1: (id 1)
  -- runTest "Test 6: infer eempty cempty ((/\\a. (\\x. x : a -> a)) 1)" $
  --   trace2 $ \ty env ->
  --     let a = inject (TyNom 0)
  --         x = inject (Nom 1)
  --         idTerm = tlam (bindT a (ann (lam (bindT x (var x))) (tarr (tvar a) (tvar a))))
  --     in goal $ infer eempty cempty (app idTerm (lit (inject (1 :: Int)))) ty env

  -- -- Test 7: id with type application: id @Int
  -- runTest "Test 7: infer eempty cempty ((/\\a. (\\x. x : a -> a)) @Int)" $
  --   trace2 $ \ty env ->
  --     let a = inject (TyNom 0)
  --         x = inject (Nom 1)
  --         idTerm = tlam (bindT a (ann (lam (bindT x (var x))) (tarr (tvar a) (tvar a))))
  --     in goal $ infer eempty cempty (tapp idTerm tint) ty env

  -- -- Test 8: id @Int applied to 1: id @Int 1
  -- runTest "Test 8: infer eempty cempty (((/\\a. (\\x. x : a -> a)) @Int) 1)" $
  --   trace2 $ \ty env ->
  --     let a = inject (TyNom 0)
  --         x = inject (Nom 1)
  --         idTerm = tlam (bindT a (ann (lam (bindT x (var x))) (tarr (tvar a) (tvar a))))
  --     in goal $ infer eempty cempty (app (tapp idTerm tint) (lit (inject (1 :: Int)))) ty env

  -- -- Test 9: sub eempty (forall a. a -> a) (ctm 1 cempty)
  -- runTest "Test 9: sub eempty (forall a. a -> a) (ctm 1 cempty)" $
  --   trace2 $ \env' resultTy ->
  --     let a = inject (TyNom 0)
  --     in goal $ sub eempty (tforall (bindT a (tarr (tvar a) (tvar a)))) (ctm (lit (inject (1 :: Int))) cempty) env' resultTy

  -- Test 10: infer (bot <: a <: top) (ctype a) (lit 1)
  runTest "Test 10: infer (ebound bot a top eempty) (ctype a) (lit 1)" $
    trace2 $ \ty env' ->
      let a = inject (TyNom 0)
      in goal $ infer (ebound tbot a ttop eempty) (ctype (tvar a)) (lit (inject (1 :: Int))) ty env'

  -- Test 11: sub (bot <: a <: top) int (ctype a)
  runTest "Test 11: sub (ebound bot a top eempty) int (ctype a)" $
    trace2 $ \env' resultTy ->
      let a = inject (TyNom 0)
      in goal $ sub (ebound tbot a ttop eempty) tint (ctype (tvar a)) env' resultTy

  runTestDet "Test 11 new: sub (ebound bot a top eempty) int (ctype a)" $
    trace0Det $ fresh $ \env' ->
      let a = inject (TyNom 0)
      in goal $ ssub (ebound tbot a ttop eempty) tint neg (tvar a) (T S.empty env')

  -- -- Test 12: updateLower (bot <: a <: top) a int
  -- runTest1 "Test 12: updateLower (ebound bot a top eempty) a int" $
  --   trace1 $ \env' ->
  --     let a = inject (TyNom 0)
  --     in goal $ updateLower (ebound tbot a ttop eempty) a tint env'

  -- Test 13: ssub failure trace (arr rule matches, then gets stuck on top <: int)
  runTestDet "Test 13: ssub eempty (int→int) ≤⁺ (top→top)  (expected fail)" $
    trace0Det $ fresh $ \env' ->
      goal $ ssub eempty (tarr tint tint) pos (tarr ttop ttop) (T S.empty env')

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
