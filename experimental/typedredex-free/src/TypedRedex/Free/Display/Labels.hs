{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Display DSL using OverloadedLabels.
--
-- Users write display rules using labels that match smart constructor names:
--
-- @
-- {-# LANGUAGE OverloadedLabels #-}
--
-- tmDisplay :: Display Tm
-- tmDisplay = display
--   [ #var  ~> \\n -> "var " <> n
--   , #unit ~> "()"
--   , #lam  ~> \\b -> "λ. " <> b
--   , #app  ~> \\(f, x) -> f <> " " <> x
--   , #ann  ~> \\(e, t) -> e <> " : " <> t
--   ]
-- @
--
-- The labels (#var, #lam, etc.) match the smart constructor names,
-- avoiding any naming conflicts or redundant suffixes.
module TypedRedex.Free.Display.Labels
  ( -- * Display Expression
    D(..)
  , renderD
  , (<+>)
    -- * Labels
  , Tag(..)
    -- * Display Rules
  , DisplayRule(..)
  , (~>)
  , (~=)
  , Display(..)
  , display
  , lookupDisplay
    -- * Arity Adaptation
  , ToDisplayFn(..)
    -- * Combinators
  , parens
  , brackets
  , commaSep
  ) where

import Data.String (IsString(..))
import GHC.OverloadedLabels (IsLabel(..))
import GHC.TypeLits (Symbol, KnownSymbol, symbolVal)
import Data.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- Display Expression
--------------------------------------------------------------------------------

-- | Display expression: a template for rendering terms.
data D
  = Lit String
  | Seq D D
  | Parens D
  | Empty
  deriving (Show, Eq)

instance IsString D where
  fromString = Lit

instance Semigroup D where
  Empty <> y = y
  x <> Empty = x
  x <> y     = Seq x y

instance Monoid D where
  mempty = Empty

-- | D-specific concatenation operator.
--
-- Use this instead of '<>' to avoid type ambiguity with OverloadedStrings:
--
-- @
-- #var ~> \\n -> "var " <+> n   -- n is inferred as D
-- @
(<+>) :: D -> D -> D
(<+>) = (<>)

infixr 6 <+>

-- | Render a display expression to string.
renderD :: D -> String
renderD (Lit s)     = s
renderD (Seq a b)   = renderD a ++ renderD b
renderD (Parens d)  = "(" ++ renderD d ++ ")"
renderD Empty       = ""

-- | Wrap in parentheses
parens :: D -> D
parens = Parens

-- | Wrap in brackets
brackets :: D -> D
brackets d = "[" <> d <> "]"

-- | Comma-separated
commaSep :: [D] -> D
commaSep []     = Empty
commaSep [x]    = x
commaSep (x:xs) = x <> ", " <> commaSep xs

--------------------------------------------------------------------------------
-- Labels
--------------------------------------------------------------------------------

-- | A label that carries a constructor name at both type and value level.
--
-- With OverloadedLabels, @#foo@ becomes @fromLabel \@"foo"@ which gives
-- us a @Tag@ containing the string "foo".
newtype Tag = Tag String
  deriving (Show, Eq)

instance KnownSymbol name => IsLabel name Tag where
  fromLabel = Tag (symbolVal (Proxy @name))

--------------------------------------------------------------------------------
-- Arity Adaptation
--------------------------------------------------------------------------------

-- | Convert various function signatures to @[D] -> D@.
--
-- Supports:
--   * Nullary: @D@
--   * Unary:   @D -> D@
--   * Binary:  @(D, D) -> D@
--   * Ternary: @(D, D, D) -> D@
--   * etc.
class ToDisplayFn a where
  toDisplayFn :: a -> [D] -> D

-- Nullary (constant) - D itself
instance ToDisplayFn D where
  toDisplayFn d _ = d

-- Unary - function from D to D
instance ToDisplayFn (D -> D) where
  toDisplayFn f (a:_) = f a
  toDisplayFn f []    = f (Lit "?")

-- Binary (tuple) - function from (D,D) to D
instance ToDisplayFn ((D, D) -> D) where
  toDisplayFn f (a:b:_) = f (a, b)
  toDisplayFn f [a]     = f (a, Lit "?")
  toDisplayFn f []      = f (Lit "?", Lit "?")

-- Ternary (tuple)
instance ToDisplayFn ((D, D, D) -> D) where
  toDisplayFn f (a:b:c:_) = f (a, b, c)
  toDisplayFn f _         = Lit "?"

-- Quaternary (tuple)
instance ToDisplayFn ((D, D, D, D) -> D) where
  toDisplayFn f (a:b:c:d:_) = f (a, b, c, d)
  toDisplayFn f _           = Lit "?"

--------------------------------------------------------------------------------
-- Display Rules
--------------------------------------------------------------------------------

-- | A display rule: constructor name paired with formatting function.
data DisplayRule a = DisplayRule
  { ruleName :: String
  , ruleBody :: [D] -> D
  }

-- | Create a display rule from a label and formatting function.
--
-- @
-- #app ~> \\(f, x) -> f <> " " <> x
-- @
(~>) :: ToDisplayFn f => Tag -> f -> DisplayRule a
(~>) (Tag name) f = DisplayRule name (toDisplayFn f)

infixr 0 ~>

-- | Variant for nullary constructors with explicit D type
(~=) :: Tag -> D -> DisplayRule a
(~=) (Tag name) d = DisplayRule name (const d)

infixr 0 ~=

--------------------------------------------------------------------------------
-- Display Table
--------------------------------------------------------------------------------

-- | A display specification for type @a@: a list of rules.
newtype Display a = Display { unDisplay :: [DisplayRule a] }

-- | Create a display table from a list of rules.
display :: [DisplayRule a] -> Display a
display = Display

-- | Look up a display function by constructor name.
lookupDisplay :: String -> Display a -> Maybe ([D] -> D)
lookupDisplay name (Display rules) =
  case [ruleBody r | r <- rules, ruleName r == name] of
    (f:_) -> Just f
    []    -> Nothing
