{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Minimal display class for logic types.
--
-- This module defines the 'HasDisplay' class which allows types to specify
-- how their constructors should be formatted. The actual Display DSL is in
-- typedredex-interp; this module just provides the interface that Field uses.
module TypedRedex.Logic.Display
  ( HasDisplay(..)
  , defaultFormatCon
  ) where

import Data.Typeable (Typeable)

-- | Types that know how to display themselves.
--
-- The 'formatCon' method takes a constructor name and already-rendered
-- children, and produces a formatted string.
--
-- Instances are typically defined using the Display DSL from
-- TypedRedex.Interp.Display.
class Typeable a => HasDisplay a where
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
