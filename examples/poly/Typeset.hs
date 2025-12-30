{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Typesetting for ssub rules with proper variable naming.
--
-- This module provides:
-- 1. NamingConfig for type-specific variable names (Γ, Δ for Env; A, B for Ty; etc.)
-- 2. TermFormatter for term presentation
--
-- Note: Judgment formatting is handled automatically by the DSL -
-- format functions are defined alongside judgments in Rules.hs.
module Typeset
  ( PolyFormatter(..)
  , polyNaming
  ) where

import TypedRedex.Interp.Typesetting
import TypedRedex.Interp.Format (TermFormatter(..))
import TypedRedex.Interp.Display (formatWithDisplay)
import TypedRedex.Interp.PrettyPrint (NamingConfig, emptyNaming, namingFor, cycleNames, numberedNames)
import TypedRedex.DSL.Moded (toApplied)
import TypedRedex.DSL.Define (appGoal)
import TypedRedex.Nominal.Prelude (TyNom, Nom)

import Syntax (Ty, Env, Polar, tyDisplay, polarDisplay, envDisplay)
import Rules

--------------------------------------------------------------------------------
-- Naming Configuration
--------------------------------------------------------------------------------

-- | Variable naming for the poly example.
--
-- Uses Greek letters for environments, uppercase for types, etc.
polyNaming :: NamingConfig
polyNaming
  = namingFor @Env    (numberedNames "Γ")
  $ namingFor @Ty     (cycleNames ["A", "B", "C", "D", "E", "F"])
  $ namingFor @Polar  (cycleNames ["p", "q"])
  $ namingFor @TyNom  (cycleNames ["α", "β", "γ", "δ"])
  $ namingFor @Nom    (cycleNames ["x", "y", "z", "w"])
  $ emptyNaming

--------------------------------------------------------------------------------
-- Formatter using Display DSL
--------------------------------------------------------------------------------

-- | Formatter for poly example.
--
-- Only needs TermFormatter for syntax (types, environments, polarity).
-- Judgment formatting is automatic - format functions are defined
-- alongside judgments in Rules.hs.
data PolyFormatter = PolyFormatter

instance TermFormatter PolyFormatter where
  formatTerm _ name args =
    -- Try each display table in order
    case formatWithDisplay tyDisplay name args of
      Just s  -> Just s
      Nothing -> case formatWithDisplay polarDisplay name args of
        Just s  -> Just s
        Nothing -> case formatWithDisplay envDisplay name args of
          Just s  -> Just s
          Nothing -> Nothing  -- fall back to default

-- No JudgmentFormatter instance needed!
-- Format functions are defined in Rules.hs with defJudgeN.
