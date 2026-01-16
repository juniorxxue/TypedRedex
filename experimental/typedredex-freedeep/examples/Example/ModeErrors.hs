{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QualifiedDo #-}

module Example.ModeErrors (modeErrorExample) where

import TypedRedex.Backend.Eval (eval, query, qfresh)
import TypedRedex.DSL
import qualified TypedRedex.DSL as R
import Support.Nat

f :: Judgment "f" '[I, O] '[Nat, Nat]
f = judgment
  [ rule "f-base" $ R.do
      (x, y) <- R.fresh
      R.concl $ f x y
  ]

bad :: Judgment "bad" '[I, O] '[Nat, Nat]
bad = judgment
  [ rule "bad-ghost" $ R.do
      ghost <- R.fresh
      out <- R.fresh
      R.concl $ bad zro out
      R.prem  $ f ghost out
  ]

-- Example runtime error (shape):
-- Mode error in rule bad-ghost
--   conclusion: bad(zro, ?n)
--   cannot schedule premises
--   blocked vars: ?n
--   ghost inputs (never produced): ?n
--   blocked premises:
--     - f ?n ?m
modeErrorExample :: IO ()
modeErrorExample = do
  let q = query $ do
        out <- qfresh
        pure (bad zro out, out)
  print (eval q)
