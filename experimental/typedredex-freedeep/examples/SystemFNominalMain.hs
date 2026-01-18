module Main (main) where

import TypedRedex.Backend.Eval (eval, query, qfresh)
import TypedRedex.Interp.Trace (TraceResult(..), prettyDerivation, trace)
import TypedRedex.Interp.Typeset (typeset)
import TypedRedex.Nominal.Bind (Bind(..))
import TypedRedex.Nominal.Prelude (TyNom(..), tynom)

import Example.SystemFNominal as SF
import Support.Nat (zro, suc)

assertElem :: (Eq a, Show a) => String -> a -> [a] -> IO ()
assertElem name expected xs =
  if expected `elem` xs
    then putStrLn ("[ok] " ++ name)
    else error ("[fail] " ++ name ++ ": expected " ++ show expected ++ ", got " ++ show xs)

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
  putStrLn (typeset (infer ctxEmpty idTm idTy))

  let a0 = TyNom 0
      idTyVal = TyForall (Bind a0 (TyArr (TyVar a0) (TyVar a0)))
      tmId = idTm
      tmIdInt = app (tapp idTm tint) (intLit (suc zro))
      tmIdPoly = app (tapp idTm idTy) idTm
      tyIdAlpha = tforall (tynom 1) (tarr (tvar (tynom 1)) (tvar (tynom 1)))

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

  putStrLn ""
  putStrLn "=== Done ==="
