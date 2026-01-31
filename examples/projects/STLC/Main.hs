module STLC.Main (main) where

import System.Exit (exitFailure)
import Test.QuickCheck (Result(..), quickCheckWithResult)
import TypedRedex.Backend.Eval (query, qfresh)
import TypedRedex.Interp.MCheck (mcheck)
import TypedRedex.Interp.Trace (TraceResult(..), prettyDerivation, trace)
import TypedRedex.Interp.Typeset (typeset)
import TypedRedex.Nominal.Prelude (nom)

import STLC.Properties (prop_preservation, prop_progress, qcArgs)
import STLC.Rules (addNat, lookupVar, step, subst, typeof, value)
import STLC.Syntax
import Support.Nat (zro, suc)

main :: IO ()
main = do
  putStrLn "=== STLC ==="
  putStrLn ""

  putStrLn "=== Typeset ==="
  putStrLn ""
  putStrLn (typeset addNat)
  putStrLn (typeset lookupVar)
  putStrLn (typeset typeof)
  putStrLn (typeset value)
  putStrLn (typeset subst)
  putStrLn (typeset step)

  putStrLn ""
  putStrLn "=== Mode Check ==="
  putStrLn ""
  putStrLn ("addNat: " ++ mcheck addNat)
  putStrLn ("lookup: " ++ mcheck lookupVar)
  putStrLn ("typeof: " ++ mcheck typeof)
  putStrLn ("value:  " ++ mcheck value)
  putStrLn ("subst:  " ++ mcheck subst)
  putStrLn ("step:   " ++ mcheck step)

  putStrLn ""
  putStrLn "=== QuickCheck ==="
  putStrLn ""

  r1 <- quickCheckWithResult qcArgs prop_progress
  r2 <- quickCheckWithResult qcArgs prop_preservation
  requireSuccess r1
  requireSuccess r2

  -- Trace example: if (\x:Bool. \y:Int. 1 + true) true 1 then 1 else 2
  -- This should fail with a type error at "1 + true"
  putStrLn ""
  putStrLn "=== Trace (type failure) ==="
  putStrLn ""
  let one = suc zro
      two = suc one
      x = nom 0
      y = nom 1
      -- \x:Bool. \y:Int. 1 + true
      badBody = plus (lit one) true
      innerLam = lam tint y badBody
      outerLam = lam tbool x innerLam
      -- (\x:Bool. \y:Int. 1 + true) true 1
      applied = app (app outerLam true) (lit one)
      -- if ... then 1 else 2
      expr = ifte applied (lit one) (lit two)

  let qTypeof = query $ do
        ty <- qfresh
        pure (typeof eempty expr ty, ty)
  printTrace "if (\\x:Bool. \\y:Int. 1 + true) true 1 then 1 else 2" (trace qTypeof)

  putStrLn ""
  putStrLn "=== Done ==="
  where
    requireSuccess :: Result -> IO ()
    requireSuccess r =
      case r of
        Success{} -> pure ()
        _ -> exitFailure

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

