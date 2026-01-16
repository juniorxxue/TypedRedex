{-# LANGUAGE DataKinds #-}

module Main (main) where

import TypedRedex.Backend.Eval (eval, query, qfresh)
import TypedRedex.Interp.Trace (prettyDerivation, trace)
import qualified Example.Stlc as Stlc
import qualified Example.Pcf as Pcf
import qualified Example.Poly as Poly
import Support.Nat (Nat(..))

assertEqual :: (Eq a, Show a) => String -> a -> a -> IO ()
assertEqual name expected actual =
  if expected == actual
    then putStrLn ("[ok] " ++ name)
    else error ("[fail] " ++ name ++ "\n  expected: " ++ show expected ++ "\n  actual:   " ++ show actual)

assertBool :: String -> Bool -> IO ()
assertBool name ok =
  if ok
    then putStrLn ("[ok] " ++ name)
    else error ("[fail] " ++ name)

main :: IO ()
main = do
  putStrLn "=== TypedRedex FreeDeep Tests ==="

  -- STLC: unit
  let qStlcUnit = query $ do
        ty <- qfresh
        pure (Stlc.infer Stlc.ctxEmpty Stlc.unit ty, ty)
  assertEqual "stlc unit" [Stlc.TyUnit] (eval qStlcUnit)

  -- STLC: id unit
  let qStlcId = query $ do
        ty <- qfresh
        pure (Stlc.infer Stlc.ctxEmpty Stlc.idUnit ty, ty)
  assertEqual "stlc id" [Stlc.TyArr Stlc.TyUnit Stlc.TyUnit] (eval qStlcId)

  -- STLC: (id unit)
  let qStlcApp = query $ do
        ty <- qfresh
        pure (Stlc.infer Stlc.ctxEmpty Stlc.appIdUnit ty, ty)
  assertEqual "stlc app" [Stlc.TyUnit] (eval qStlcApp)

  -- PCF: 1 + 2 = 3
  let qPcfAdd = query $ do
        v <- qfresh
        pure (Pcf.evalP (Pcf.plus Pcf.one Pcf.two) v, v)
  assertEqual "pcf add" [Pcf.Succ (Pcf.Succ (Pcf.Succ Pcf.Zero))] (eval qPcfAdd)

  -- PCF: if0 0 then 1 else 2 => 1
  let qPcfIf0 = query $ do
        v <- qfresh
        pure (Pcf.evalP (Pcf.if0 Pcf.zero Pcf.one Pcf.two) v, v)
  assertEqual "pcf if0" [Pcf.Succ Pcf.Zero] (eval qPcfIf0)

  -- PCF: pred (succ (succ 0)) => succ 0
  let qPcfPred = query $ do
        v <- qfresh
        pure (Pcf.evalP (Pcf.predTm (Pcf.succTm (Pcf.succTm Pcf.zero))) v, v)
  assertEqual "pcf pred" [Pcf.Succ Pcf.Zero] (eval qPcfPred)

  -- Poly/System F: infer polyId
  let qPolyId = query $ do
        ty <- qfresh
        pure (Poly.infer Poly.cempty Poly.polyId ty, ty)
  assertEqual "poly id" [Poly.TyForall Z (Poly.TyArr (Poly.TyVar Z) (Poly.TyVar Z))] (eval qPolyId)

  -- Poly/System F: infer (polyId [Int])
  let qPolyApp = query $ do
        ty <- qfresh
        pure (Poly.infer Poly.cempty Poly.polyIdApp ty, ty)
  assertEqual "poly app" [Poly.TyArr Poly.TyInt Poly.TyInt] (eval qPolyApp)

  -- Trace sanity check
  let traces = trace qStlcUnit
  assertBool "trace nonempty" (not (null traces))
  case traces of
    [] -> pure ()
    (_, deriv):_ ->
      assertBool "trace pretty" (not (null (prettyDerivation deriv)))

  putStrLn "=== All tests passed ==="
