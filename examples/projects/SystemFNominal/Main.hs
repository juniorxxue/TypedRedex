module SystemFNominal.Main (main) where

import TypedRedex.Backend.Eval (eval, query, qfresh)
import TypedRedex.Interp.Trace (TraceResult(..), prettyDerivation, trace)
import TypedRedex.Interp.Typeset (typeset)
import TypedRedex.Nominal.Bind (Bind(..))
import TypedRedex.Nominal.Prelude (TyNom(..), nom, tynom)

import SystemFNominal.Rules
import SystemFNominal.Syntax
import Support.Nat (zro, suc)

assertElem :: (Eq a, Show a) => String -> a -> [a] -> IO ()
assertElem name expected xs =
  if expected `elem` xs
    then putStrLn ("[ok] " ++ name)
    else error ("[fail] " ++ name ++ ": expected " ++ show expected ++ ", got " ++ show xs)

assertNonEmpty :: Show a => String -> [a] -> IO ()
assertNonEmpty name xs =
  if null xs
    then error ("[fail] " ++ name ++ ": expected results, got " ++ show xs)
    else putStrLn ("[ok] " ++ name)

assertEmpty :: Show a => String -> [a] -> IO ()
assertEmpty name xs =
  if null xs
    then putStrLn ("[ok] " ++ name)
    else error ("[fail] " ++ name ++ ": expected no results, got " ++ show xs)

expectTraceOk :: String -> [TraceResult a] -> IO ()
expectTraceOk name results =
  case results of
    TraceOk _ _ : _ -> putStrLn ("[ok] trace " ++ name)
    TraceFail _ _ : _ -> error ("[fail] trace " ++ name)
    [] -> error ("[fail] trace " ++ name ++ ": no results")

printTrace :: String -> [TraceResult a] -> IO ()
printTrace name results =
  case results of
    TraceOk _ deriv : _ -> do
      putStrLn ("--- trace " ++ name ++ " ---")
      putStrLn (prettyDerivation deriv)
    TraceFail _ deriv : _ -> do
      putStrLn ("--- trace " ++ name ++ " (failed) ---")
      putStrLn (prettyDerivation deriv)
    [] -> putStrLn ("--- trace " ++ name ++ " (no results) ---")

main :: IO ()
main = do
  putStrLn "=== System F (Nominal) ==="
  putStrLn ""
  putStrLn (typeset infer)
  putStrLn $ typeset tyEquiv
  putStrLn $ typeset tmEquiv
  putStrLn $ typeset tySubst

  let a0 = TyNom 0
      idTyVal = TyForall (Bind a0 (TyArr (TyVar a0) (TyVar a0)))
      tmId = idTm
      tmIdInt = app (tapp idTm tint) (intLit (suc zro))
      tmIdPoly = app (tapp idTm idTy) idTm
      tyIdAlpha = tforall (tynom 1) (tarr (tvar (tynom 1)) (tvar (tynom 1)))
      tyFree1 = tforall (tynom 0) (tvar (tynom 1))
      tyFree2 = tforall (tynom 2) (tvar (tynom 1))
      tyCapture = tforall (tynom 1) (tvar (tynom 1))
      tyOuter1 = tforall (tynom 0) (tforall (tynom 1) (tvar (tynom 0)))
      tyOuter2 = tforall (tynom 1) (tforall (tynom 0) (tvar (tynom 1)))
      tyInner = tforall (tynom 0) (tforall (tynom 1) (tvar (tynom 1)))
      tyArrFree1 = tforall (tynom 0) (tarr (tvar (tynom 2)) (tvar (tynom 0)))
      tyArrFree2 = tforall (tynom 3) (tarr (tvar (tynom 2)) (tvar (tynom 3)))
      x0 = nom 0
      x1 = nom 1
      tmLamAlpha1 = lam tunit x0 (var x0)
      tmLamAlpha2 = lam tunit x1 (var x1)
      tmLamFree = lam tunit x0 (var x1)
      tmLamCapture = lam tunit x1 (var x1)
      tmNestedOuter1 = lam tunit x0 (lam tunit x1 (var x0))
      tmNestedOuter2 = lam tunit x1 (lam tunit x0 (var x1))
      tmNestedInner1 = lam tunit x0 (lam tunit x1 (var x1))
      tmNestedInner2 = lam tunit x1 (lam tunit x0 (var x1))
      tmTyAlpha1 = tlam (tynom 0) (lam (tvar (tynom 0)) x0 (var x0))
      tmTyAlpha2 = tlam (tynom 1) (lam (tvar (tynom 1)) x1 (var x1))
      tmTyFree = tlam (tynom 0) (lam (tvar (tynom 1)) x0 (var x0))
      tmTyCapture = tlam (tynom 1) (lam (tvar (tynom 1)) x0 (var x0))
      tmLamTyAlpha1 = lam idTy x0 (var x0)
      tmLamTyAlpha2 = lam tyIdAlpha x1 (var x1)
      tmTappAlpha1 = tapp tmId idTy
      tmTappAlpha2 = tapp tmId tyIdAlpha

  -- 1. id
  let qId = query $ do
        ty <- qfresh
        pure (infer ctxEmpty tmId ty, ty)
      traceId = trace qId
  printTrace "id" traceId
  assertElem "id" idTyVal (eval qId)
  expectTraceOk "id" traceId

  -- 2. id @Int 1
  let qIdInt = query $ do
        ty <- qfresh
        pure (infer ctxEmpty tmIdInt ty, ty)
  let traceIdInt = trace qIdInt
  printTrace "id @Int 1" traceIdInt
  assertElem "id @Int 1" TyInt (eval qIdInt)
  expectTraceOk "id @Int 1" traceIdInt

  -- 3. id @(forall a. a -> a) id
  let qIdPoly = query $ do
        ty <- qfresh
        pure (infer ctxEmpty tmIdPoly ty, ty)
  let traceIdPoly = trace qIdPoly
  printTrace "id @(forall a. a -> a) id" traceIdPoly
  assertElem "id @(forall a. a -> a) id" idTyVal (eval qIdPoly)
  expectTraceOk "id @(forall a. a -> a) id" traceIdPoly

  -- 4. type equivalence (alpha-equivalence stress test)
  let qTyEq = query $ pure (tyEquiv idTy tyIdAlpha, idTy)
      traceTyEq = trace qTyEq
  printTrace "type equiv id" traceTyEq
  assertElem "type equiv id" idTyVal (eval qTyEq)
  expectTraceOk "type equiv id" traceTyEq

  -- 5. type equivalence (free vars + nesting)
  let qTyFree = query $ pure (tyEquiv tyFree1 tyFree2, tyFree1)
  assertNonEmpty "type equiv free var" (eval qTyFree)

  let qTyCapture = query $ pure (tyEquiv tyFree1 tyCapture, tyFree1)
  assertEmpty "type equiv free vs bound" (eval qTyCapture)

  let qTyOuter = query $ pure (tyEquiv tyOuter1 tyOuter2, tyOuter1)
  assertNonEmpty "type equiv nested outer" (eval qTyOuter)

  let qTyInner = query $ pure (tyEquiv tyOuter1 tyInner, tyOuter1)
  assertEmpty "type equiv nested mismatch" (eval qTyInner)

  let qTyArrFree = query $ pure (tyEquiv tyArrFree1 tyArrFree2, tyArrFree1)
  assertNonEmpty "type equiv free in arrow" (eval qTyArrFree)

  -- 6. term equivalence (alpha + free vars)
  let qTmLamAlpha = query $ pure (tmEquiv tmLamAlpha1 tmLamAlpha2, tmLamAlpha1)
  assertNonEmpty "term equiv lam alpha" (eval qTmLamAlpha)

  let qTmLamCapture = query $ pure (tmEquiv tmLamFree tmLamCapture, tmLamFree)
  assertEmpty "term equiv free vs bound" (eval qTmLamCapture)

  let qTmNestedOuter = query $ pure (tmEquiv tmNestedOuter1 tmNestedOuter2, tmNestedOuter1)
  assertNonEmpty "term equiv nested outer" (eval qTmNestedOuter)

  let qTmNestedInner = query $ pure (tmEquiv tmNestedInner1 tmNestedInner2, tmNestedInner1)
  assertEmpty "term equiv nested mismatch" (eval qTmNestedInner)

  let qTmTyAlpha = query $ pure (tmEquiv tmTyAlpha1 tmTyAlpha2, tmTyAlpha1)
  assertNonEmpty "term equiv type alpha" (eval qTmTyAlpha)

  let qTmTyCapture = query $ pure (tmEquiv tmTyFree tmTyCapture, tmTyFree)
  assertEmpty "term equiv type free vs bound" (eval qTmTyCapture)

  let qTmLamTyAlpha = query $ pure (tmEquiv tmLamTyAlpha1 tmLamTyAlpha2, tmLamTyAlpha1)
  assertNonEmpty "term equiv type ann alpha" (eval qTmLamTyAlpha)

  let qTmTappAlpha = query $ pure (tmEquiv tmTappAlpha1 tmTappAlpha2, tmTappAlpha1)
  assertNonEmpty "term equiv tapp type alpha" (eval qTmTappAlpha)

  putStrLn ""
  putStrLn "=== Done ==="
