module Poly.Main (main) where

import TypedRedex.Backend.Eval (eval, query, qfresh)
import TypedRedex.Interp.Trace (TraceResult(..), prettyDerivation, trace)
import TypedRedex.Interp.Typeset (typeset)

import Poly.Rules (infer, lookupCtx, tySubst, polyId, polyIdApp)
import Poly.Syntax (cempty)

main :: IO ()
main = do
  putStrLn "=== Poly ==="
  putStrLn ""
  putStrLn (typeset lookupCtx)
  putStrLn (typeset tySubst)
  putStrLn (typeset infer)

  let qId = query $ do
        ty <- qfresh
        pure (infer cempty polyId ty, ty)
  let qApp = query $ do
        ty <- qfresh
        pure (infer cempty polyIdApp ty, ty)

  putStrLn "--- eval polyId ---"
  print (eval qId)

  putStrLn "--- trace polyId ---"
  case trace qId of
    TraceOk _ deriv : _ -> putStrLn (prettyDerivation deriv)
    TraceFail _ deriv : _ -> putStrLn (prettyDerivation deriv)
    [] -> putStrLn "(no results)"

  putStrLn "--- eval polyIdApp ---"
  print (eval qApp)

  putStrLn "--- trace polyIdApp ---"
  case trace qApp of
    TraceOk _ deriv : _ -> putStrLn (prettyDerivation deriv)
    TraceFail _ deriv : _ -> putStrLn (prettyDerivation deriv)
    [] -> putStrLn "(no results)"
