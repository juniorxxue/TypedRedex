module LTI.Main
  ( main
  ) where

import TypedRedex.Interp.Typeset (typeset)

import LTI.Rules (sub, subList)

main :: IO ()
main = do
  putStrLn "=== LTI Subtyping ==="
  putStrLn ""
  putStrLn (typeset sub)
  putStrLn (typeset subList)
