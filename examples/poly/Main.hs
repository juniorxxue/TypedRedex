{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}

-- | Poly Type Inference - Polarized Subtyping Tests
-- Matches Poly's ssub :: (Env, Env) -> Ty -> Polar -> Ty -> m Env
module Main (main) where

import TypedRedex
import TypedRedex.Nominal.Prelude
import TypedRedex.Interp.Subst (runSubstRedex, takeS, Stream)
import TypedRedex.Interp.Tracing (runWithDerivationWith, prettyDerivationWith, Derivation(..), JudgmentFormatter(..), defaultFormatConclusion)
import qualified TypedRedex.DSL.Fresh as F
import TypedRedex.DSL.Moded (AppliedM(..), toApplied, ground)

import TypedRedex.Interp.Typesetting
import TypedRedex.Interp.Format (TermFormatter(..), JudgmentFormatter(..), defaultFormatJudgment)


import Syntax
import Rules
import Typeset

--------------------------------------------------------------------------------
-- Judgment Formatter
--------------------------------------------------------------------------------

data PolyFormatter = PolyFormatter

instance JudgmentFormatter PolyFormatter where
  formatJudgment _ name args = case (name, args) of
    ("ssub", [env, senv, ty1, p, ty2, senv']) ->
      "(" ++ env ++ ", " ++ senv ++ ") ⊢ " ++ ty1 ++ " " ++ p ++ " " ++ ty2 ++ " ⊣ " ++ senv'
    ("isEvar", [env, a]) ->
      a ++ "^ ∈ " ++ env
    ("inst", [env, a, ty, env']) ->
      env ++ "[" ++ a ++ " := " ++ ty ++ "] = " ++ env'
    _ -> defaultFormatConclusion name args

instance TermFormatter PolyFormatter where
  formatTerm _ name args = case (name, args) of
    -- Types
    ("TInt", []) -> Just "int"
    ("TBool", []) -> Just "bool"
    ("TVar", [n]) -> Just n
    ("TArr", [a, b]) -> Just $ "(" ++ a ++ " -> " ++ b ++ ")"
    -- Polarity
    ("Pos", []) -> Just "≤+"
    ("Neg", []) -> Just "≤-"
    -- Environment (matches Poly's Show instance)
    ("EEmpty", []) -> Just "∅"
    ("ETrm", [x, ty, env]) -> Just $ env ++ ", " ++ x ++ ":" ++ ty
    ("EUvar", [a, env]) -> Just $ env ++ ", " ++ a
    ("EEvar", [a, env]) -> Just $ env ++ ", " ++ a ++ "^"
    ("ESvar", [a, ty, env]) -> Just $ env ++ ", " ++ a ++ "=" ++ ty
    -- Nominal atoms
    ('a':rest, []) | all isDigit rest -> Just $ "a" ++ rest
    ('x':rest, []) | all isDigit rest -> Just $ "x" ++ rest
    _ -> Nothing
    where
      isDigit c = c `elem` "0123456789"

prettyDerivation :: Derivation -> String
prettyDerivation = prettyDerivationWith PolyFormatter

--------------------------------------------------------------------------------
-- Running queries
-- Matches Poly's: ssub (env, senv) ty1 polar ty2 => senv'
--------------------------------------------------------------------------------

ssubIO :: Env -> Env -> Ty -> Polar -> Ty -> Stream Env
ssubIO env0 senv0 ty1_0 p0 ty2_0 = runSubstRedex $ F.fresh $ \senv' -> do
  let envL  = Ground $ project env0
      senvL = Ground $ project senv0
      ty1L  = Ground $ project ty1_0
      pL    = Ground $ project p0
      ty2L  = Ground $ project ty2_0
  appGoal $ toApplied $ ssub (ground envL) (ground senvL) (ground ty1L) (ground pL) (ground ty2L) (ground senv')
  eval senv'

type TracingStream a = Stream (a, Derivation)

ssubWithTrace :: Env -> Env -> Ty -> Polar -> Ty -> TracingStream Env
ssubWithTrace env0 senv0 ty1_0 p0 ty2_0 = runWithDerivationWith PolyFormatter $ F.fresh $ \senv' -> do
  let envL  = Ground $ project env0
      senvL = Ground $ project senv0
      ty1L  = Ground $ project ty1_0
      pL    = Ground $ project p0
      ty2L  = Ground $ project ty2_0
  appGoal $ toApplied $ ssub (ground envL) (ground senvL) (ground ty1L) (ground pL) (ground ty2L) (ground senv')
  eval senv'

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "=== Extracted rules for ssub ===\n"
  printSsubRules