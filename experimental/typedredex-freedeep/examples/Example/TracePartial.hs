{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE OverloadedStrings #-}

module Example.TracePartial (tracePartialExample) where

import TypedRedex.Backend.Eval (Query, query)
import TypedRedex.Interp.Trace (TraceResult(..), prettyDerivation, trace)
import TypedRedex.DSL
import qualified TypedRedex.DSL as R
import TypedRedex.Pretty ((<+>))
import qualified Example.Stlc as Stlc
import qualified Example.StlcPlus as StlcPlus
import Support.Nat (Nat, zro, suc)

--------------------------------------------------------------------------------
-- Tiny search-tree example (two-premise chain)
--------------------------------------------------------------------------------

g :: Judgment "g" '[I, O] '[Nat, Nat]
g = judgment $ do
  format $ \x y -> x <+> " ~g~ " <+> y
  rules
    [ rule "g-refl" $ R.do
        x <- R.fresh
        R.concl $ g x x
    ]

h :: Judgment "h" '[I, O] '[Nat, Nat]
h = judgment $ do
  format $ \x y -> x <+> " ~h~ " <+> y
  rules
    [ rule "h-chain" $ R.do
        (x, y, z) <- R.fresh
        R.concl $ h x z
        R.prem  $ g x y
        R.prem  $ g y z
    ]

neqDemo :: Judgment "neqDemo" '[I, I] '[Nat, Nat]
neqDemo = judgment $ do
  format $ \x y -> x <+> " != " <+> y
  rules
    [ rule "neq-demo" $ R.do
        (x, y) <- R.fresh
        R.concl $ neqDemo x y
        x =/= y
    ]

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

tracePartialExample :: IO ()
tracePartialExample = do
  putStrLn "=== Partial derivation examples ==="
  runCase "stlc-var-empty" $ query $
    pure (Stlc.infer Stlc.ctxEmpty (Stlc.var zro) Stlc.tunit, Stlc.tunit)
  runCase "stlc-plus-lam" $ query $
    pure
      ( StlcPlus.infer
          StlcPlus.ctxEmpty
          StlcPlus.lamAdd1
          (StlcPlus.tarr StlcPlus.tint StlcPlus.tint)
      , StlcPlus.tint
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
