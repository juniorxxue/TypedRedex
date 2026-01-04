{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Minimal display class for logic types.
--
-- This module defines the 'HasDisplay' class which allows types to specify
-- how their constructors should be formatted. The actual Display DSL is in
-- typedredex-interp; this module just provides the interface that Field uses.
module TypedRedex.Logic.Display
  ( -- * Variable naming (for typesetting)
    VarNames
  , subscriptNum
  , subscriptStr
  , cycleNames
  , numberedNames
  , numberedNames'
    -- * Term formatting (for pretty-printing)
  , HasDisplay(..)
  , defaultFormatCon
  ) where

import Data.Typeable (Typeable)

--------------------------------------------------------------------------------
-- Variable naming (infinite lists)
--------------------------------------------------------------------------------

-- | Infinite list of variable names.
--
-- All naming schemes produce infinite lists, so indexing is always safe.
type VarNames = [String]

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

-- | Create names that cycle through a list, adding subscripts on overflow.
--
-- @
-- cycleNames ["A", "B", "C"]
--   = ["A", "B", "C", "A₁", "B₁", "C₁", "A₂", "B₂", "C₂", ...]
-- @
cycleNames :: [String] -> VarNames
cycleNames [] = numberedNames "?"  -- Fallback for empty list
cycleNames bases =
  [ base ++ suffix i
  | i <- [0..]
  , base <- bases
  ]
  where
    suffix 0 = ""
    suffix n = subscriptNum n

-- | Create numbered names, with the first one unsubscripted.
--
-- @
-- numberedNames "τ" = ["τ", "τ₁", "τ₂", "τ₃", ...]
-- @
numberedNames :: String -> VarNames
numberedNames sym = sym : [sym ++ subscriptNum i | i <- [1..]]

-- | Backwards-compatible alias for 'numberedNames'.
numberedNames' :: String -> VarNames
numberedNames' = numberedNames

-- | Types that know how to display themselves.
--
-- The 'formatCon' method takes a constructor name and already-rendered
-- children, and produces a formatted string.
--
-- Instances are typically defined using the Display DSL from
-- TypedRedex.Interp.Display.
class Typeable a => HasDisplay a where
  -- | Variable naming scheme for this type (used by the typesetting interpreter).
  --
  -- The list must be infinite; helpers like 'cycleNames' and 'numberedNames'
  -- make this easy.
  typeNaming :: VarNames
  typeNaming = numberedNames "?"

  -- | Format a constructor given its name and already-rendered children.
  --
  -- Returns 'Just' the formatted string, or 'Nothing' to use default formatting.
  formatCon :: String -> [String] -> Maybe String
  formatCon _ _ = Nothing  -- default: use fallback

-- | Default formatting: @name(arg1, arg2, ...)@
defaultFormatCon :: String -> [String] -> String
defaultFormatCon name [] = name
defaultFormatCon name args = name ++ "(" ++ intercalate ", " args ++ ")"
  where
    intercalate _ [] = ""
    intercalate _ [x] = x
    intercalate sep (x:xs) = x ++ sep ++ intercalate sep xs
