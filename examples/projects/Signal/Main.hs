module Signal.Main (main) where

import TypedRedex.Interp.Typeset (typeset)

import Signal.Rules
  ( flipPolar
  , envConcat
  , lookupTmVar
  , lookupUvar
  , lookupEvar
  , lookupSvar
  , inst
  )

main :: IO ()
main = do
  putStrLn "=== Signal Auxiliary Judgments ==="
  putStrLn ""

  putStrLn "--- flipPolar ---"
  putStrLn (typeset flipPolar)
  putStrLn ""

  putStrLn "--- envConcat ---"
  putStrLn (typeset envConcat)
  putStrLn ""

  putStrLn "--- lookupTmVar ---"
  putStrLn (typeset lookupTmVar)
  putStrLn ""

  putStrLn "--- lookupUvar ---"
  putStrLn (typeset lookupUvar)
  putStrLn ""

  putStrLn "--- lookupEvar ---"
  putStrLn (typeset lookupEvar)
  putStrLn ""

  putStrLn "--- lookupSvar ---"
  putStrLn (typeset lookupSvar)
  putStrLn ""

  putStrLn "--- inst ---"
  putStrLn (typeset inst)
  putStrLn ""

  putStrLn "=== Done ==="
