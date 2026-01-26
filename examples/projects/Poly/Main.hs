module Poly.Main (main) where

import TypedRedex.Backend.Eval (eval, query, qfresh)
import TypedRedex.Interp.Trace (TraceResult(..), prettyDerivation, trace)
import TypedRedex.Interp.MCheck (mcheck)

import TypedRedex.Interp.Typeset (typeset)
import TypedRedex.Nominal.Prelude (nom, tynom)

import Poly.Rules (infer, ssub, sub)
import Poly.Syntax
import Support.Nat (zro, suc)

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
  putStrLn "=== Poly ==="
  putStrLn ""
  -- putStrLn (typeset ssub)
  -- putStrLn (typeset sub)
  -- putStrLn $ mcheck infer

  let one = suc zro
      x0 = nom 0
      a0 = tynom 0
      idLam = lam x0 (var x0)
      idAnn = ann idLam (tarr tint tint)
      idApp = app idAnn (lit one)
      idAppUnann = app idLam (lit one)


  -- Test: id (g 1) and g (id 1) where g : forall b. int -> b, id : forall a. a -> a
  let gVar = nom 1
      idVar = nom 2
      b0 = tynom 1
      -- g : forall b. int -> b
      gTy = tforall b0 (tarr tint (tvar b0))
      -- id : forall a. a -> a
      idTy = tforall a0 (tarr (tvar a0) (tvar a0))
      -- environment with g and id
      envGId = etrm gVar gTy (etrm idVar idTy eempty)
      -- id (g 1)
      idGApp = app (var idVar) (app (var gVar) (lit one))

  -- let qPolyIdGTop = query $ do
  --       env <- qfresh
  --       pure (infer envGId (ctype ttop) idGApp ttop env, ttop)
  -- printTrace "infer id (g 1) : top (ctx top)" (trace qPolyIdGTop)
  -- assertNonEmpty "infer id (g 1) : top (ctx top)" (eval qPolyIdGTop)

  -- Test: envGId |- forall a. a -> a <: [g 1] ~> []
  let qSubForallIdG = query $ do
        env <- qfresh
        ty <- qfresh
        pure (sub envGId idTy (ctm (app (var gVar) (lit one)) cempty) env ty, (env, ty))
  printTrace "sub envGId (forall a. a -> a) <: [g 1] ~> []" (trace qSubForallIdG)
  assertNonEmpty "sub envGId (forall a. a -> a) <: [g 1] ~> []" (eval qSubForallIdG)


  putStrLn ""
  putStrLn "=== Done ==="
