module ModeErrors.Main (main) where

import Control.Exception (SomeException, displayException, evaluate, try)
import TypedRedex.Backend.Eval (eval, query, qfresh)
import TypedRedex.Interp.Trace (TraceResult(..), prettyDerivation, trace)
import TypedRedex.Interp.Typeset (typeset)

import ModeErrors.Rules (bad, f)
import ModeErrors.Syntax (Nat, zro)

main :: IO ()
main = do
  putStrLn "=== Mode Errors ==="
  putStrLn ""
  putStrLn (typeset f)
  putStrLn (typeset bad)

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

  putStrLn "--- eval bad (expected error) ---"
  result <- try (evaluate (eval qBad)) :: IO (Either SomeException [Nat])
  case result of
    Left err -> putStrLn (displayException err)
    Right xs -> print xs
