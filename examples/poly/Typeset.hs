{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}

-- | Typesetting for ssub rules with proper variable naming.
--
-- This module provides:
-- 1. NamingConfig for type-specific variable names (Γ, Δ for Env; A, B for Ty; etc.)
-- 2. TermFormatter for domain-specific syntax (arrows, products, etc.)
-- 3. JudgmentFormatter for judgment presentation (⊢, ⊣, etc.)
module Typeset
  ( SsubFormatter(..)
  , polyNaming
  , printSsubRules
  ) where

import TypedRedex.Interp.Typesetting
import TypedRedex.Interp.Format (TermFormatter(..), JudgmentFormatter(..), defaultFormatJudgment)
import TypedRedex.Interp.PrettyPrint (NamingConfig, emptyNaming, namingFor, cycleNames, numberedNames)
import TypedRedex.DSL.Moded (toApplied)
import TypedRedex.DSL.Define (appGoal)
import TypedRedex.Nominal.Prelude (TyNom, Nom)

import Syntax
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
-- Formatter for ssub (domain-specific term/judgment formatting)
--------------------------------------------------------------------------------

data SsubFormatter = SsubFormatter

instance TermFormatter SsubFormatter where
  formatTerm _ name args = case (name, args) of
    -- Types
    ("TInt", []) -> Just "int"
    ("TBool", []) -> Just "bool"
    ("TVar", [a]) -> Just a
    ("TArr", [a, b]) -> Just $ "(" ++ a ++ " → " ++ b ++ ")"
    ("TList", [a]) -> Just $ "[" ++ a ++ "]"
    ("TProd", [a, b]) -> Just $ "(" ++ a ++ " × " ++ b ++ ")"
    ("TForall", [bnd]) -> Just $ "∀" ++ bnd
    -- Polarity
    ("Pos", []) -> Just "≤⁺"
    ("Neg", []) -> Just "≤⁻"
    -- Environment
    ("EEmpty", []) -> Just "·"
    ("ETrm", [x, ty, env]) -> Just $ env ++ ", " ++ x ++ ":" ++ ty
    ("EUvar", [a, env]) -> Just $ env ++ ", " ++ a
    ("EEvar", [a, env]) -> Just $ env ++ ", " ++ a ++ "̂"
    ("ESvar", [a, ty, env]) -> Just $ env ++ ", " ++ a ++ "=" ++ ty
    -- Bind (for TForall)
    ("Bind", [nm, body]) -> Just $ nm ++ "." ++ body
    -- Nominal atoms - pass through
    _ -> Nothing

instance JudgmentFormatter SsubFormatter where
  formatJudgment _ name args = case (name, args) of
    -- ssub: Γ; Δ ⊢ A ≤p B ⊣ Δ'
    ("ssub", [env, senv, ty1, p, ty2, senv']) ->
      env ++ "; " ++ senv ++ " ⊢ " ++ ty1 ++ " " ++ formatPolar p ++ " " ++ ty2 ++ " ⊣ " ++ senv'
    -- isEvar: α̂ ∈ Δ
    ("isEvar", [env, a]) ->
      a ++ "̂ ∈ " ++ env
    -- isSvar: α = τ ∈ Δ
    ("isSvar", [env, a, ty]) ->
      a ++ " = " ++ ty ++ " ∈ " ++ env
    -- inst: Δ[α̂ := τ] = Δ'
    ("inst", [env, a, ty, env']) ->
      env ++ "[" ++ a ++ "̂ := " ++ ty ++ "] = " ++ env'
    -- flipPolar: p̄ = p'
    ("flipPolar", [p, p']) ->
      formatPolarBar p ++ " = " ++ formatPolarVal p'
    -- equality/disequality
    ("==", [a, b]) -> a ++ " = " ++ b
    ("=/=", [a, b]) -> a ++ " ≠ " ++ b
    _ -> defaultFormatJudgment name args
    where
      -- Format polarity for subtyping relation
      formatPolar p
        | p == "≤⁺" = "≤⁺"
        | p == "≤⁻" = "≤⁻"
        | otherwise = "≤"
      -- Format polarity with bar for flip premise
      formatPolarBar p
        | p == "≤⁺" = "⁺̄"
        | p == "≤⁻" = "⁻̄"
        | otherwise = p ++ "̄"
      -- Format polar value (without ≤)
      formatPolarVal p
        | p == "≤⁺" = "⁺"
        | p == "≤⁻" = "⁻"
        | otherwise = p

--------------------------------------------------------------------------------
-- Convenience function to print rules
--------------------------------------------------------------------------------

-- | Print extracted rules for ssub with proper naming.
printSsubRules :: IO ()
printSsubRules = do
  let applied = toApplied $
        ssub (modedVar 0) (modedVar 1) (modedVar 2) (modedVar 3) (modedVar 4) (modedVar 5)
  printRules polyNaming SsubFormatter "ssub" (appGoal applied)
