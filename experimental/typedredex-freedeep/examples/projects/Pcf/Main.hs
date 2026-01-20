module Pcf.Main (main) where

import TypedRedex.Backend.Eval (eval, query, qfresh)
import TypedRedex.Interp.Trace (TraceResult(..), prettyDerivation, trace)
import TypedRedex.Interp.Typeset (typeset)

import Pcf.Rules (add, evalP)
import Pcf.Syntax (plus, one, two)

main :: IO ()
main = do
  putStrLn "=== PCF ==="
  putStrLn ""
  putStrLn (typeset add)
  putStrLn (typeset evalP)

  let q = query $ do
        v <- qfresh
        pure (evalP (plus one two) v, v)

  putStrLn "--- eval plus one two ---"
  print (eval q)

  putStrLn "--- trace plus one two ---"
  case trace q of
    TraceOk _ deriv : _ -> putStrLn (prettyDerivation deriv)
    TraceFail _ deriv : _ -> putStrLn (prettyDerivation deriv)
    [] -> putStrLn "(no results)"
