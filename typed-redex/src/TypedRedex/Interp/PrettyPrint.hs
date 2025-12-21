{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Pretty-printing utilities for variable naming and subscript conversion.
--
-- This module centralizes all display-related naming logic, keeping it
-- separate from core logic and interpreters.
module TypedRedex.Interp.PrettyPrint
  ( -- * Subscript conversion
    subscriptNum
  , subscriptStr
    -- * Variable naming bundles
  , VarNaming(..)
  , ctxNaming
  , tyNaming
  , tmNaming
  , natNaming
  , nomNaming
  , tyNomNaming
  , defaultNaming
  , namingByTag
    -- * Variable naming functions (for direct use)
  , ctxVarName
  , tyVarName
  , tmVarName
  , natVarName
  , nomVarName
  , tyNomVarName
  , defaultVarName
    -- * Type class for variable naming
  , LogicVarNaming(..)
  ) where

import Data.Maybe (fromMaybe)
import Data.List (find)

-- | Convert an Int to subscript digits.
-- @subscriptNum 42 = "₄₂"@
subscriptNum :: Int -> String
subscriptNum = subscriptStr . show

-- | Convert a String of digits to subscript.
-- @subscriptStr "123" = "₁₂₃"@
subscriptStr :: String -> String
subscriptStr = concatMap toSub
  where
    toSub '0' = "₀"; toSub '1' = "₁"; toSub '2' = "₂"; toSub '3' = "₃"
    toSub '4' = "₄"; toSub '5' = "₅"; toSub '6' = "₆"; toSub '7' = "₇"
    toSub '8' = "₈"; toSub '9' = "₉"; toSub c = [c]

--------------------------------------------------------------------------------
-- Variable naming bundles
--------------------------------------------------------------------------------

-- | A bundle of variable naming info: a tag for identification and a naming function.
-- Use pre-defined bundles (ctxNaming, tyNaming, etc.) to ensure consistency.
data VarNaming = VarNaming
  { vnTag  :: String          -- ^ Tag for variable categorization (e.g., "C", "T", "E")
  , vnName :: Int -> String   -- ^ Naming function: index -> display name
  }

-- | Context naming: tag "C", names Γ, Γ₁, Γ₂, ...
ctxNaming :: VarNaming
ctxNaming = VarNaming "C" ctxVarName

-- | Type naming: tag "T", names A, B, C, D, E, F, A₁, ...
tyNaming :: VarNaming
tyNaming = VarNaming "T" tyVarName

-- | Term/expression naming: tag "E", names e, e₁, e₂, ...
tmNaming :: VarNaming
tmNaming = VarNaming "E" tmVarName

-- | Natural number naming: tag "N", names n, m, k, n₁, ...
natNaming :: VarNaming
natNaming = VarNaming "N" natVarName

-- | Nom (term variable name) naming: tag "X", names x, y, z, x₁, y₁, z₁, ...
nomNaming :: VarNaming
nomNaming = VarNaming "X" nomVarName

-- | TyNom (type variable name) naming: tag "A", names α, β, σ, α₁, β₁, σ₁, ...
tyNomNaming :: VarNaming
tyNomNaming = VarNaming "A" tyNomVarName

-- | Default naming: tag "V", names v₀, v₁, v₂, ...
defaultNaming :: VarNaming
defaultNaming = VarNaming "V" defaultVarName

-- | All known naming schemes (for tag lookup)
allNamings :: [VarNaming]
allNamings = [ctxNaming, tyNaming, tmNaming, natNaming, nomNaming, tyNomNaming, defaultNaming]

-- | Look up a naming scheme by its tag. Returns defaultNaming if not found.
namingByTag :: String -> VarNaming
namingByTag tag = fromMaybe defaultNaming $ find (\n -> vnTag n == tag) allNamings

--------------------------------------------------------------------------------
-- Variable naming functions
--------------------------------------------------------------------------------

-- | Context variables: Γ, Γ₁, Γ₂, ...
ctxVarName :: Int -> String
ctxVarName 0 = "Γ"
ctxVarName i = "Γ" ++ subscriptNum i

-- | Type variables: A, B, C, D, E, F, A₁, B₁, ...
tyVarName :: Int -> String
tyVarName i = let (q, r) = i `divMod` 6
                  base = ["A", "B", "C", "D", "E", "F"] !! r
              in if q == 0 then base else base ++ subscriptNum q

-- | Term/expression variables: e, e₁, e₂, ...
tmVarName :: Int -> String
tmVarName 0 = "e"
tmVarName i = "e" ++ subscriptNum i

-- | Natural number variables: n, m, k, n₁, m₁, k₁, ...
natVarName :: Int -> String
natVarName i = let (q, r) = i `divMod` 3
                   base = ["n", "m", "k"] !! r
               in if q == 0 then base else base ++ subscriptNum q

-- | Nom (term variable name) variables: x, y, z, x₁, y₁, z₁, ...
nomVarName :: Int -> String
nomVarName i = let (q, r) = i `divMod` 3
                   base = ["x", "y", "z"] !! r
               in if q == 0 then base else base ++ subscriptNum q

-- | TyNom (type variable name) variables: α, β, σ, α₁, β₁, σ₁, ...
tyNomVarName :: Int -> String
tyNomVarName i = let (q, r) = i `divMod` 3
                     base = ["α", "β", "σ"] !! r
                 in if q == 0 then base else base ++ subscriptNum q

-- | Default variable naming: v₀, v₁, v₂, ...
defaultVarName :: Int -> String
defaultVarName n = "v" ++ subscriptNum n

--------------------------------------------------------------------------------
-- Type class for variable naming
--------------------------------------------------------------------------------

-- | Type class for specifying how logic variables of a type should be named.
--
-- Separate from LogicType to allow user customization without affecting
-- the core logic type machinery.
--
-- Default instance uses tmNaming (e, e₁, e₂, ...).
class LogicVarNaming a where
  varNaming :: VarNaming
  varNaming = tmNaming
