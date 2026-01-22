module Simple.Main (main) where

import TypedRedex.Backend.Eval (eval, query, qfresh)
import TypedRedex.Interp.Trace (TraceResult(..), prettyDerivation, trace)
import TypedRedex.Interp.Typeset (typeset)

import Simple.Rules (add)
import Simple.Syntax (zro, suc)

main :: IO ()
main = do
  putStrLn "=== Simple: Nat Addition ==="
  putStrLn ""
  putStrLn (typeset add)

  let q = query $ do
        out <- qfresh
        pure (add (suc zro) (suc (suc zro)) out, out)

  putStrLn "--- eval ---"
  print (eval q)

  putStrLn "--- trace ---"
  case trace q of
    TraceOk _ deriv : _ -> putStrLn (prettyDerivation deriv)
    TraceFail _ deriv : _ -> putStrLn (prettyDerivation deriv)
    [] -> putStrLn "(no results)"
