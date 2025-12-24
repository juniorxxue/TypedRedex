{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Pretty-printing utilities for variable naming and subscript conversion.
--
-- This module centralizes all display-related naming logic, keeping it
-- separate from core logic and interpreters.
module TypedRedex.Interp.PrettyPrint
  ( -- * Subscript conversion
    subscriptNum
  , subscriptStr
    -- * Type class for typesetting variable naming
  , TypesetNaming(..)
    -- * Helpers for defining naming schemes
  , cycleNames
  ) where

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
-- Typesetting variable naming
--------------------------------------------------------------------------------

-- | Type class for customizing how logic variables appear in typeset rules.
--
-- Example:
--
-- @
-- instance TypesetNaming Env where
--   typesetName = cycleNames [\"Γ\", \"Δ\", \"Θ\"]
--
-- instance TypesetNaming Ty where
--   typesetName = cycleNames [\"A\", \"B\", \"C\", \"D\", \"E\", \"F\"]
-- @
--
-- Default uses e, e₁, e₂, ...
class TypesetNaming a where
  typesetName :: Int -> String
  typesetName 0 = "e"
  typesetName i = "e" ++ subscriptNum i

--------------------------------------------------------------------------------
-- Helpers for defining naming schemes
--------------------------------------------------------------------------------

-- | Create a naming function that cycles through a list of base names,
-- adding subscripts when the list is exhausted.
--
-- @
-- cycleNames [\"Γ\", \"Δ\", \"Θ\"] 0 = \"Γ\"
-- cycleNames [\"Γ\", \"Δ\", \"Θ\"] 1 = \"Δ\"
-- cycleNames [\"Γ\", \"Δ\", \"Θ\"] 2 = \"Θ\"
-- cycleNames [\"Γ\", \"Δ\", \"Θ\"] 3 = \"Γ₁\"
-- cycleNames [\"Γ\", \"Δ\", \"Θ\"] 4 = \"Δ₁\"
-- @
cycleNames :: [String] -> Int -> String
cycleNames bases i =
  let n = length bases
      (q, r) = i `divMod` n
      base = bases !! r
  in if q == 0 then base else base ++ subscriptNum q
