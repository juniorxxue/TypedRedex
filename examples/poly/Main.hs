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

  tryTypeset "flipPolar"      $ typeset2 polyConfig flipPolar
  tryTypeset "lookupTmVar"    $ typeset3 polyConfig lookupTmVar
  tryTypeset "lookupUvar"     $ typeset2 polyConfig lookupUvar
  tryTypeset "lookupBoundVar" $ typeset4 polyConfig lookupBoundVar
  tryTypeset "glb"            $ typeset3 polyConfig glb
  tryTypeset "lub"            $ typeset3 polyConfig lub
  tryTypeset "updateUpper"    $ typeset4 polyConfig updateUpper
  tryTypeset "updateLower"    $ typeset4 polyConfig updateLower
  tryTypeset "inst"           $ typeset5 polyConfig inst
  tryTypeset "instP"          $ typeset6 polyConfig instP
  tryTypeset "ssub"           $ typeset5 polyConfig ssub
  tryTypeset "sub"            $ typeset5 polyConfig sub
  tryTypeset "infer"          $ typeset5 polyConfig infer
