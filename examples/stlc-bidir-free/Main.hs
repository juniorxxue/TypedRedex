{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoRebindableSyntax #-}

-- | Bidirectional STLC with Indexed Free Monad DSL
--
-- This example demonstrates how rules are defined using the indexed free monad
-- approach, where do-notation builds a pure AST that can be interpreted
-- multiple ways.
module Main (main) where

import Prelude
import Rules

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "=== Indexed Free Monad DSL Demo ==="
  putStrLn ""
  putStrLn "This example demonstrates mode-checked bidirectional typing"
  putStrLn "rules defined using the indexed free monad approach."
  putStrLn ""
  putStrLn "Key differences from typedredex-dsl:"
  putStrLn "  1. Do-notation builds a pure IxFree AST"
  putStrLn "  2. No execution during rule construction"
  putStrLn "  3. Multiple interpreters for the same AST:"
  putStrLn "     - Eval: standard execution"
  putStrLn "     - Typeset: rule extraction"
  putStrLn "     - Trace: derivation trees"
  putStrLn ""
  putStrLn "Defined judgments:"
  putStrLn "  - lookupCtx :: Judgment3 (I, I, O) Ctx Nat Ty"
  putStrLn "  - synth     :: Judgment3 (I, I, O) Ctx Tm Ty"
  putStrLn "  - check     :: Judgment3 (I, I, I) Ctx Tm Ty"
  putStrLn "  - notInCtx  :: Judgment2 (I, I) Ctx Nat"
  putStrLn ""
  putStrLn "All rules compile, proving mode correctness at compile time!"
  putStrLn ""
  putStrLn "Note: Full interpreter integration requires typedredex-interp"
  putStrLn "to be updated to use typedredex-free."
