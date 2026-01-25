module ModeErrors.Main (main) where

import TypedRedex.Backend.Eval (eval, query, qfresh)
import TypedRedex.Interp.MCheck (mcheck)
import TypedRedex.Interp.Trace (TraceResult(..), prettyDerivation, trace)
import TypedRedex.Interp.Typeset (typeset)

import ModeErrors.Rules (bad, f)
import ModeErrors.Syntax (zro)

main :: IO ()
main = do
  putStrLn "=== Mode Errors ==="
  putStrLn ""
  putStrLn (typeset f)
  putStrLn (typeset bad)
  putStrLn "--- mcheck f ---"
  putStrLn (mcheck f)
  putStrLn "--- mcheck bad ---"
  putStrLn (mcheck bad)

  let qOk = query $ do
        out <- qfresh
        pure (f zro out, out)

  putStrLn "--- eval f ---"
  print (eval qOk)

  putStrLn "--- trace f ---"
  case trace qOk of
    TraceOk _ deriv : _ -> putStrLn (prettyDerivation deriv)
    TraceFail _ deriv : _ -> putStrLn (prettyDerivation deriv)
    [] -> putStrLn "(no results)"

  let qBad = query $ do
        out <- qfresh
        pure (bad zro out, out)

  putStrLn "--- eval bad ---"
  print (eval qBad)
