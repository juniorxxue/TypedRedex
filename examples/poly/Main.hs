{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Poly Type Inference - Print Extracted Inference Rules
module Main (main) where

import Control.Exception (catch, SomeException)

import Rules
import Typeset

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

-- | Try to print rules, handling exceptions gracefully
tryTypeset :: String -> IO () -> IO ()
tryTypeset name action = do
  putStrLn $ "--- " ++ name ++ " ---\n"
  action `catch` \(e :: SomeException) ->
    putStrLn $ "(some rules could not be typeset: " ++ take 50 (show e) ++ "...)\n"

main :: IO ()
main = do
  putStrLn "=== Extracted Inference Rules for Poly ===\n"

  tryTypeset "flipPolar"      $ typeset2 flipPolar
  tryTypeset "lookupTmVar"    $ typeset3 lookupTmVar
  tryTypeset "lookupUvar"     $ typeset2 lookupUvar
  tryTypeset "lookupBoundVar" $ typeset4 lookupBoundVar
  tryTypeset "glb"            $ typeset3 glb
  tryTypeset "lub"            $ typeset3 lub
  tryTypeset "updateUpper"    $ typeset4 updateUpper
  tryTypeset "updateLower"    $ typeset4 updateLower
  tryTypeset "inst"           $ typeset5 inst
  tryTypeset "instP"          $ typeset6 instP
  tryTypeset "ssub"           $ typeset5 ssub
  tryTypeset "sub"            $ typeset5 sub
  tryTypeset "infer"          $ typeset5 infer
