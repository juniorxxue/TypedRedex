{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ImplicitParams #-}

module Main (main) where

import Control.Applicative (empty)
import TypedRedex.Core.Redex hiding (rule2, rule3)
import TypedRedex.Core.Internal.Logic (Logic (Ground), LogicType (..))
import TypedRedex.Interpreters.SubstRedex (runSubstRedex, takeS, Stream)
import TypedRedex.Interpreters.TracingRedex (runWithDerivation, prettyDerivation, Derivation(..))
import TypedRedex.Utils.Type (quote0, quote1, quote2)
import TypedRedex.Utils.Define (rule2, rule3)

import Syntax

--------------------------------------------------------------------------------
-- Relations using the new judgment/rule syntax
--------------------------------------------------------------------------------

-- Nat equality check
natEq :: (Redex rel) => L Nat rel -> L Nat rel -> Applied2 rel Nat Nat
natEq = judgment2 "natEq" [natEqZero, natEqSucc]
  where
    natEqZero = rule2 "eq-zero" $
      concl $ natEq zro zro

    natEqSucc = rule2 "eq-succ" $ fresh2 $ \n' m' -> do
      concl $ natEq (suc n') (suc m')
      prem  $ natEq n' m'

-- Less than check (strict)
natLt :: (Redex rel) => L Nat rel -> L Nat rel -> Applied2 rel Nat Nat
natLt = judgment2 "natLt" [natLtZero, natLtSucc]
  where
    natLtZero = rule2 "lt-zero" $ fresh $ \m' ->
      concl $ natLt zro (suc m')

    natLtSucc = rule2 "lt-succ" $ fresh2 $ \n' m' -> do
      concl $ natLt (suc n') (suc m')
      prem  $ natLt n' m'

-- Context lookup
lookupTm :: (Redex rel) => L Ctx rel -> L Nat rel -> L Ty rel -> Applied3 rel Ctx Nat Ty
lookupTm = judgment3 "lookupTm" [lookupTmHere, lookupTmThere, lookupTmSkip]
  where
    lookupTmHere = rule3 "lookup-here" $ fresh2 $ \ty rest ->
      concl $ lookupTm (tmBind ty rest) zro ty

    lookupTmThere = rule3 "lookup-there" $ fresh4 $ \ty ty' rest n' -> do
      concl $ lookupTm (tmBind ty' rest) (suc n') ty
      prem  $ lookupTm rest n' ty

    lookupTmSkip = rule3 "lookup-skip" $ fresh3 $ \rest n ty -> do
      concl $ lookupTm (tyBind rest) n ty
      prem  $ lookupTm rest n ty

--------------------------------------------------------------------------------
-- Type substitution (using old relation style for comparison)
--------------------------------------------------------------------------------

substTy :: (Redex rel) => L Nat rel -> L Ty rel -> L Ty rel -> L Ty rel -> Relation rel
substTy = relation4 "substTy" $ \depth subTy ty result ->
  conde
    [ do ty <=> tunit; result <=> tunit
    , fresh $ \n -> do
        ty <=> tvar n
        call $ substTyVar depth subTy n result
    , fresh4 $ \a b a' b' -> do
        ty <=> tarr a b
        call $ substTy depth subTy a a'
        call $ substTy depth subTy b b'
        result <=> tarr a' b'
    , fresh3 $ \body body' depth' -> do
        ty <=> tall body
        depth' <=> suc depth
        call $ substTy depth' subTy body body'
        result <=> tall body'
    ]

substTyVar :: (Redex rel) => L Nat rel -> L Ty rel -> L Nat rel -> L Ty rel -> Relation rel
substTyVar = relation4 "substTyVar" $ \depth subTy n result ->
  conde
    [ do prem $ natEq n depth; result <=> subTy
    , do prem $ natLt n depth; result <=> tvar n
    , fresh $ \n' -> do
        prem $ natLt depth n
        n <=> suc n'
        result <=> tvar n'
    ]

addNat :: (Redex rel) => L Nat rel -> L Nat rel -> L Nat rel -> Relation rel
addNat = relation3 "addNat" $ \n m sum' ->
  conde
    [ do n <=> zro; sum' <=> m
    , fresh2 $ \n' sum'' -> do
        n <=> suc n'
        sum' <=> suc sum''
        call $ addNat n' m sum''
    ]

shiftTy :: (Redex rel) => L Nat rel -> L Nat rel -> L Ty rel -> L Ty rel -> Relation rel
shiftTy = relation4 "shiftTy" $ \cutoff amount ty result ->
  conde
    [ do ty <=> tunit; result <=> tunit
    , fresh $ \n -> do
        ty <=> tvar n
        call $ shiftTyVar cutoff amount n result
    , fresh4 $ \a b a' b' -> do
        ty <=> tarr a b
        call $ shiftTy cutoff amount a a'
        call $ shiftTy cutoff amount b b'
        result <=> tarr a' b'
    , fresh3 $ \body body' cutoff' -> do
        ty <=> tall body
        cutoff' <=> suc cutoff
        call $ shiftTy cutoff' amount body body'
        result <=> tall body'
    ]

shiftTyVar :: (Redex rel) => L Nat rel -> L Nat rel -> L Nat rel -> L Ty rel -> Relation rel
shiftTyVar = relation4 "shiftTyVar" $ \cutoff amount n result ->
  conde
    [ do prem $ natLt n cutoff; result <=> tvar n
    , fresh $ \n' -> do
        conde [ prem $ natEq n cutoff, prem $ natLt cutoff n ]
        call $ addNat n amount n'
        result <=> tvar n'
    ]

--------------------------------------------------------------------------------
-- Type checking (using old relation style)
--------------------------------------------------------------------------------

typeof :: (Redex rel) => L Ctx rel -> L Tm rel -> L Ty rel -> Relation rel
typeof = relation3 "typeof" $ \ctx e ty ->
  conde
    [ do e <=> unit'; ty <=> tunit
    , fresh $ \n -> do
        e <=> var n
        prem $ lookupTm ctx n ty
    , fresh3 $ \tyA body tyB -> do
        e <=> lam tyA body
        ty <=> tarr tyA tyB
        call $ typeof (tmBind tyA ctx) body tyB
    , fresh3 $ \e1 e2 tyA -> do
        e <=> app e1 e2
        call $ typeof ctx e1 (tarr tyA ty)
        call $ typeof ctx e2 tyA
    , fresh2 $ \body tyA -> do
        e <=> tlam body
        ty <=> tall tyA
        call $ typeof (tyBind ctx) body tyA
    , fresh4 $ \e' tyB tyA tyA' -> do
        e <=> tapp e' tyB
        call $ typeof ctx e' (tall tyA)
        call $ substTy zro tyB tyA tyA'
        ty <=> tyA'
    ]

--------------------------------------------------------------------------------
-- Running queries
--------------------------------------------------------------------------------

typeofIO :: Ctx -> Tm -> Stream Ty
typeofIO ctx0 e0 = runSubstRedex $ fresh $ \ty -> do
  _ <- embed $ typeof (Ground $ project ctx0) (Ground $ project e0) ty
  eval ty

checkIII :: Ctx -> Tm -> Ty -> Stream ()
checkIII ctx0 e0 ty0 = runSubstRedex $ do
  _ <- embed $ typeof (Ground $ project ctx0) (Ground $ project e0) (Ground $ project ty0)
  pure ()

-- Run with derivation tracing
typeofWithTrace :: Ctx -> Tm -> Stream (Ty, Derivation)
typeofWithTrace ctx0 e0 = runWithDerivation $ fresh $ \ty -> do
  _ <- embed $ typeof (Ground $ project ctx0) (Ground $ project e0) ty
  eval ty

-- Test natLt with derivation
natLtWithTrace :: Nat -> Nat -> Stream ((), Derivation)
natLtWithTrace n m = runWithDerivation $ do
  app2Goal $ natLt (Ground $ project n) (Ground $ project m)
  pure ()

-- Test lookupTm with derivation
lookupWithTrace :: Ctx -> Nat -> Stream (Ty, Derivation)
lookupWithTrace ctx0 n0 = runWithDerivation $ fresh $ \ty -> do
  app3Goal $ lookupTm (Ground $ project ctx0) (Ground $ project n0) ty
  eval ty

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "=== System F Type Checking with Derivation Trees ==="
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

  putStrLn "=== Derivation Trees (new judgment/rule syntax) ==="
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
