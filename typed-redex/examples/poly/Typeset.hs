{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}

-- | Typesetting for ssub rules with proper variable naming.
--
-- Thanks to TypesetNaming and eager renumbering in the library,
-- this module only needs to provide custom formatters for domain-specific
-- syntax (term formatters and judgment formatters).
module Main (main) where

import TypedRedex
import TypedRedex.Interp.Typesetting
import TypedRedex.Interp.Format (TermFormatter(..), JudgmentFormatter(..), defaultFormatJudgment)
import TypedRedex.DSL.Define (appGoal)

import Syntax
import Rules

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
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "=== Extracted rules for ssub ===\n"
  let applied = modedToApplied $
        ssub (modedVar 0) (modedVar 1) (modedVar 2) (modedVar 3) (modedVar 4) (modedVar 5)
  let rules = runTypesettingWith SsubFormatter $ appGoal applied
  mapM_ (\r -> putStrLn (formatRule SsubFormatter "ssub" r) >> putStrLn "") rules
