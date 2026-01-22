module StlcPlus.Main (main) where

import TypedRedex.Backend.Eval (eval, query, qfresh)
import TypedRedex.Interp.Trace (TraceResult(..), prettyDerivation, trace)
import TypedRedex.Interp.Typeset (typeset)

import StlcPlus.Rules (infer, inferExp, lookupCtx)
import StlcPlus.Syntax (add, ctxEmpty, intLit, lam, tint, var)
import Support.Nat (zro, suc)

main :: IO ()
main = do
  putStrLn "=== STLC+ ==="
  putStrLn ""
  putStrLn (typeset lookupCtx)
  putStrLn (typeset inferExp)
  putStrLn (typeset infer)

  let goodLam = lam tint (add (var zro) (intLit (suc zro)))
  let q = query $ do
        ty <- qfresh
        pure (infer ctxEmpty goodLam ty, ty)

  putStrLn "--- eval goodLam ---"
  print (eval q)

  putStrLn "--- trace goodLam ---"
  case trace q of
    TraceOk _ deriv : _ -> putStrLn (prettyDerivation deriv)
    TraceFail _ deriv : _ -> putStrLn (prettyDerivation deriv)
    [] -> putStrLn "(no results)"
