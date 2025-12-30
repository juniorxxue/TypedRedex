{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Poly Type Inference - Polarized Subtyping Tests
-- Matches Poly's ssub :: (Env, Env) -> Ty -> Polar -> Ty -> m Env
module Main (main) where

import TypedRedex
import TypedRedex.Interp.Subst (runSubstRedex, takeS, Stream)
import TypedRedex.Interp.Tracing (runWithDerivationWith, prettyDerivationWith, Derivation(..))
import TypedRedex.Interp.Display (renderGround)
import qualified TypedRedex.DSL.Fresh as F

import Syntax
import Rules
import Typeset

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "=== Extracted rules for ssub ===\n"