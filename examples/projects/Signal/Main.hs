module Signal.Main (main) where

import TypedRedex.Interp.Typeset (typeset)
import TypedRedex.Interp.MCheck (mcheck)

import Signal.Rules

main :: IO ()
main = do
  putStrLn (typeset envConcat)
  putStrLn (typeset lookupTmVar)
  putStrLn (typeset lookupUvar)
  putStrLn (typeset lookupEvar)
  putStrLn (typeset lookupSvar)
  putStrLn (typeset inst)
  putStrLn (typeset ssub)
  putStrLn (typeset sub)
  putStrLn (typeset infer)
  putStrLn (mcheck infer)
