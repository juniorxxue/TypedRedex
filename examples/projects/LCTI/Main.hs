module LCTI.Main (main) where

import TypedRedex.Interp.Typeset (typeset)

import LCTI.Rules
  ( envConcat
  , lookupTmVar
  , lookupUvar
  , lookupEvar
  , lookupSvar
  , inst
  , closed
  , open
  , ground
  , tySubst
  , ssub
  , inferUncurry
  , sub
  , infers
  , infer
  )

main :: IO ()
main = do
  putStrLn "=== LCTI ==="
  putStrLn ""
  putStrLn (typeset envConcat)
  putStrLn (typeset lookupTmVar)
  putStrLn (typeset lookupUvar)
  putStrLn (typeset lookupEvar)
  putStrLn (typeset lookupSvar)
  putStrLn (typeset inst)
  putStrLn (typeset closed)
  putStrLn (typeset open)
  putStrLn (typeset ground)
  putStrLn (typeset tySubst)
  putStrLn (typeset ssub)
  putStrLn (typeset inferUncurry)
  putStrLn (typeset sub)
  putStrLn (typeset infers)
  putStrLn (typeset infer)
