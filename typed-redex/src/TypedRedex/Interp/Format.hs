-- | Term formatting utilities.
--
-- This module provides pretty-printing utilities for logic terms,
-- including constructor formatting and term-to-string conversion.
--
-- = Customization
--
-- Users define their own 'TermFormatter' and 'JudgmentFormatter' instances
-- in examples to control how terms and judgments are displayed.
-- The library provides only generic default formatting.
--
-- @
-- data MyFormatter = MyFormatter
--
-- instance TermFormatter MyFormatter where
--   formatTerm _ "App" [f, a] = Just $ "(" ++ f ++ " " ++ a ++ ")"
--   formatTerm _ "Lam" [b] = Just $ "(λ." ++ b ++ ")"
--   formatTerm _ _ _ = Nothing  -- fall back to default
--
-- instance JudgmentFormatter MyFormatter where
--   formatJudgment _ "typeof" [ctx, e, ty] = ctx ++ " ⊢ " ++ e ++ " : " ++ ty
--   formatJudgment _ name args = defaultFormatJudgment name args
-- @
module TypedRedex.Interp.Format
  ( -- * Term formatting
    TermFormatter(..)
  , DefaultTermFormatter(..)
  , formatCon
  , formatConWith
    -- * Judgment formatting
  , JudgmentFormatter(..)
  , defaultFormatJudgment
    -- * Logic term pretty-printing
  , prettyLogic
  , prettyLogicWith
    -- * String utilities
  , intercalate
    -- * Re-exports from PrettyPrint
  , subscriptNum
  ) where

import TypedRedex.Core.Internal.Redex
import TypedRedex.Core.Internal.Logic
import TypedRedex.Interp.PrettyPrint (subscriptStr)

-- | Re-export subscriptStr as subscriptNum for backward compatibility.
subscriptNum :: String -> String
subscriptNum = subscriptStr

--------------------------------------------------------------------------------
-- Term Formatting Typeclass
--------------------------------------------------------------------------------

-- | Typeclass for formatting term constructors.
--
-- Users implement this in their examples to control how terms are displayed.
-- Return 'Nothing' to fall back to default formatting.
--
-- @
-- instance TermFormatter MyFormatter where
--   formatTerm _ "App" [f, a] = Just $ "(" ++ f ++ " " ++ a ++ ")"
--   formatTerm _ "Lam" [ty, b] = Just $ "(λ:" ++ ty ++ ". " ++ b ++ ")"
--   formatTerm _ _ _ = Nothing  -- use default
-- @
class TermFormatter fmt where
  -- | Format a constructor application. Return 'Nothing' to use default.
  formatTerm :: fmt -> String -> [String] -> Maybe String
  formatTerm _ _ _ = Nothing

-- | Default formatter that uses generic application-style formatting.
-- Use this when you don't need custom term formatting.
data DefaultTermFormatter = DefaultTermFormatter

instance TermFormatter DefaultTermFormatter where
  formatTerm _ _ _ = Nothing

--------------------------------------------------------------------------------
-- Judgment Formatting Typeclass
--------------------------------------------------------------------------------

-- | Typeclass for formatting judgment conclusions in derivations and rules.
--
-- Users implement this in their examples to control how judgments are displayed.
-- The default implementation uses generic function-style formatting.
--
-- @
-- instance JudgmentFormatter MyFormatter where
--   formatJudgment _ "typeof" [ctx, e, ty] = ctx ++ " ⊢ " ++ e ++ " : " ++ ty
--   formatJudgment _ "step" [a, b] = a ++ " ⟶ " ++ b
--   formatJudgment _ name args = defaultFormatJudgment name args
-- @
class JudgmentFormatter fmt where
  -- | Format a judgment conclusion. The first argument is the judgment/rule name,
  -- the second is the list of arguments (already formatted as strings).
  formatJudgment :: fmt -> String -> [String] -> String
  formatJudgment _ = defaultFormatJudgment

-- | Default formatting: function-style @name(arg1, arg2, ...)@
--
-- This is the simplest possible formatting. Users should define their own
-- 'JudgmentFormatter' instances in their examples for domain-specific
-- formatting (e.g., typing judgments, step relations).
defaultFormatJudgment :: String -> [String] -> String
defaultFormatJudgment name [] = name
defaultFormatJudgment name args = name ++ "(" ++ intercalate ", " args ++ ")"

-- | Default formatter uses generic formatting for both terms and judgments.
instance JudgmentFormatter DefaultTermFormatter where
  formatJudgment _ = defaultFormatJudgment

--------------------------------------------------------------------------------
-- Constructor formatting
--------------------------------------------------------------------------------

-- | Format constructor application with a custom formatter.
formatConWith :: TermFormatter fmt => fmt -> String -> [String] -> String
formatConWith fmt name args =
  case formatTerm fmt name args of
    Just s  -> s
    Nothing -> defaultFormatCon name args

-- | Format constructor application using default formatting.
--
-- This provides generic function-style formatting: @name(arg1, arg2, ...)@
-- For domain-specific formatting (lambda, types, etc.), define a
-- 'TermFormatter' instance in your example.
formatCon :: String -> [String] -> String
formatCon = defaultFormatCon

-- | Default generic formatting: @name(arg1, arg2, ...)@
defaultFormatCon :: String -> [String] -> String
defaultFormatCon n [] = n
defaultFormatCon n args = n ++ "(" ++ intercalate ", " args ++ ")"

--------------------------------------------------------------------------------
-- Logic term pretty-printing
--------------------------------------------------------------------------------

-- | Pretty-print a logic value using quote and displayVar.
-- Uses default formatting for constructors.
prettyLogic :: (Redex rel, LogicType a) => Logic a (RVar rel) -> String
prettyLogic = prettyLogicWith DefaultTermFormatter

-- | Pretty-print a logic value with a custom term formatter.
-- Used by tracing interpreters to capture relation arguments.
prettyLogicWith :: (Redex rel, LogicType a, TermFormatter fmt) => fmt -> Logic a (RVar rel) -> String
prettyLogicWith fmt (Free v) = displayVar v
prettyLogicWith fmt (Ground r) = prettyReified fmt r
  where
    prettyReified :: (Redex rel, LogicType a, TermFormatter f) => f -> Reified a (RVar rel) -> String
    prettyReified f r' =
      let (con, fields) = quote r'
      in formatConWith f (name con) (map (prettyField f) fields)

    prettyField :: (Redex rel, TermFormatter f) => f -> Field a (RVar rel) -> String
    prettyField f (Field _ logic) = prettyLogicAny f logic

    prettyLogicAny :: (Redex rel, LogicType t, TermFormatter f) => f -> Logic t (RVar rel) -> String
    prettyLogicAny f (Free v) = displayVar v
    prettyLogicAny f (Ground r') = prettyReified f r'

--------------------------------------------------------------------------------
-- String utilities
--------------------------------------------------------------------------------

-- | Intercalate a separator between list elements.
intercalate :: String -> [String] -> String
intercalate _ [] = ""
intercalate _ [x] = x
intercalate sep (x:xs) = x ++ sep ++ intercalate sep xs
