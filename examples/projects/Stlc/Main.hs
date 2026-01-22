module Stlc.Main (main) where

import TypedRedex.Backend.Eval (eval, query, qfresh)
import TypedRedex.Interp.Trace (TraceResult(..), prettyDerivation, trace)
import TypedRedex.Interp.Typeset (typeset)

import Stlc.Rules (infer, lookupCtx, idUnit, appIdUnit)
import Stlc.Syntax (ctxEmpty)

main :: IO ()
main = do
  putStrLn "=== STLC ==="
  putStrLn ""
  putStrLn (typeset lookupCtx)
  putStrLn (typeset infer)

  let qId = query $ do
        ty <- qfresh
        pure (infer ctxEmpty idUnit ty, ty)
  let qApp = query $ do
        ty <- qfresh
        pure (infer ctxEmpty appIdUnit ty, ty)

  putStrLn "--- eval idUnit ---"
  print (eval qId)

  putStrLn "--- trace idUnit ---"
  case trace qId of
    TraceOk _ deriv : _ -> putStrLn (prettyDerivation deriv)
    TraceFail _ deriv : _ -> putStrLn (prettyDerivation deriv)
    [] -> putStrLn "(no results)"

  putStrLn "--- eval appIdUnit ---"
  print (eval qApp)

  putStrLn "--- trace appIdUnit ---"
  case trace qApp of
    TraceOk _ deriv : _ -> putStrLn (prettyDerivation deriv)
    TraceFail _ deriv : _ -> putStrLn (prettyDerivation deriv)
    [] -> putStrLn "(no results)"
