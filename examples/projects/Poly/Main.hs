module Poly.Main (main) where

import TypedRedex.Backend.Eval (eval, query, qfresh)
import TypedRedex.Interp.Trace (TraceResult(..), prettyDerivation, trace)
import TypedRedex.Nominal.Prelude (nom, tynom)

import Poly.Rules (sub)
import Poly.Syntax
import Support.Nat (zro, suc)

assertNonEmpty :: Show a => String -> [a] -> IO ()
assertNonEmpty name xs =
  if null xs
    then error ("[fail] " ++ name ++ ": expected results, got " ++ show xs)
    else putStrLn ("[ok] " ++ name)

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

  let one = suc zro
      a0 = tynom 0

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

  -- Test: envGId |- forall a. a -> a <: [g 1] ~> []
  let qSubForallIdG = query $ do
        env <- qfresh
        ty <- qfresh
        pure (sub envGId idTy (ctm (app (var gVar) (lit one)) cempty) env ty, (env, ty))
  printTrace "sub envGId (forall a. a -> a) <: [g 1] ~> []" (trace qSubForallIdG)
  assertNonEmpty "sub envGId (forall a. a -> a) <: [g 1] ~> []" (eval qSubForallIdG)


  putStrLn ""
  putStrLn "=== Done ==="
