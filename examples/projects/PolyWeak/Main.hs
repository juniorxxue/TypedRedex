module PolyWeak.Main (main) where

import TypedRedex.Backend.Eval (eval, query, qfresh)
import TypedRedex.Interp.Trace (TraceResult(..), prettyDerivation, trace)
import TypedRedex.Interp.MCheck (mcheck)

import TypedRedex.Interp.Typeset (typeset)
import TypedRedex.Nominal.Prelude (nom, tynom)

import PolyWeak.Rules (infer, ssub, sub)
import PolyWeak.Syntax
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
  putStrLn "=== Poly (Weak Invariants)==="
  putStrLn "This version is suspected to be too powerful than it should be."
  putStrLn ""
  putStrLn (typeset ssub)
  putStrLn (typeset sub)
  putStrLn $ mcheck infer

  putStrLn ""
  putStrLn "=== Subtyping ==="
  putStrLn ". |- forall a b. a -> (a -> b) -> b <: [1] -> [\\x. x] -> []"

  let one = suc zro
      x0 = nom 0
      a0 = tynom 0
      b0 = tynom 1

      revappTy =
        tforall a0 $
          tforall b0 $
            tarr (tvar a0) (tarr (tarr (tvar a0) (tvar b0)) (tvar b0))

      idLam = lam x0 (var x0)
      ctx = ctm (lit one) (ctm idLam cempty)

      qSubRevapp = query $ do
        env <- qfresh
        ty <- qfresh
        pure (sub eempty revappTy ctx env ty, (env, ty))

  printTrace "subtyping . |- forall a b. a -> (a -> b) -> b <: [1] -> [\\x. x] -> []" (trace qSubRevapp)
  assertNonEmpty "subtyping revapp" (eval qSubRevapp)


  putStrLn ""
  putStrLn "=== Done ==="
