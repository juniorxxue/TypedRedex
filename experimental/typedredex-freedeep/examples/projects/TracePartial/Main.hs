module TracePartial.Main (main) where

import TypedRedex.Backend.Eval (Query, eval, query)
import TypedRedex.Interp.Trace (TraceResult(..), prettyDerivation, trace)
import TypedRedex.Interp.Typeset (typeset)

import TracePartial.Rules (g, h, neqDemo)
import TracePartial.Syntax (zro, suc)
import qualified Stlc.Rules as Stlc
import qualified Stlc.Syntax as StlcSyn
import qualified StlcPlus.Rules as StlcPlus
import qualified StlcPlus.Syntax as StlcPlusSyn

main :: IO ()
main = do
  putStrLn "=== Trace Partial ==="
  putStrLn ""
  putStrLn (typeset g)
  putStrLn (typeset h)
  putStrLn (typeset neqDemo)
  putStrLn (typeset Stlc.infer)
  putStrLn (typeset StlcPlus.infer)

  let qOk = query $ pure (g zro zro, zro)
  putStrLn "--- eval g ---"
  print (eval qOk)

  putStrLn "--- trace g ---"
  case trace qOk of
    TraceOk _ deriv : _ -> putStrLn (prettyDerivation deriv)
    TraceFail _ deriv : _ -> putStrLn (prettyDerivation deriv)
    [] -> putStrLn "(no results)"

  putStrLn "=== Partial derivation examples ==="
  runCase "stlc-var-empty" $ query $
    pure (Stlc.infer StlcSyn.ctxEmpty (StlcSyn.var zro) StlcSyn.tunit, StlcSyn.tunit)
  runCase "stlc-plus-lam" $ query $
    pure
      ( StlcPlus.infer
          StlcPlusSyn.ctxEmpty
          StlcPlus.lamAdd1
          (StlcPlusSyn.tarr StlcPlusSyn.tint StlcPlusSyn.tint)
      , StlcPlusSyn.tint
      )
  runCase "nat-chain-stree" $ query $
    pure (h zro (suc zro), suc zro)
  runCase "neq-constraint" $ query $
    pure (neqDemo zro zro, zro)
  putStrLn "=== Done ==="

runCase :: String -> Query a -> IO ()
runCase label q = do
  putStrLn ("-- " ++ label)
  case trace q of
    TraceFail _ deriv : _ -> putStrLn (prettyDerivation deriv)
    TraceOk _ _ : _ -> error (label ++ ": expected failure, got success")
    [] -> error (label ++ ": no trace results")
  putStrLn ""
