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
-- A declarative DSL for pretty-printing logic terms, replacing verbose
-- 'TermFormatter' instances with concise pattern-based rules.
--
-- = Example Usage
--
-- @
-- {-# LANGUAGE OverloadedLabels #-}
-- {-# LANGUAGE OverloadedStrings #-}
--
-- tyDisplay :: Display Ty
-- tyDisplay = display
--   [ #tInt   ~= "int"
--   , #tBool  ~= "bool"
--   , #tVar   ~> \\a -> a
--   , #tArr   ~> \\(a, b) -> a <+> " → " <+> b
--   , #tList  ~> \\a -> "[" <+> a <+> "]"
--   , #tProd  ~> \\(a, b) -> a <+> " × " <+> b
--   ]
-- @
--
-- The labels (#tInt, #tArr, etc.) match the smart constructor names.
-- The '<+>' operator concatenates display expressions without type ambiguity.
module TypedRedex.Interp.Display
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
    -- * Integration with TermFormatter
  , formatWithDisplay
    -- * Rendering ground values (uses HasDisplay)
  , renderGround
  , renderLogic
    -- * Arity Adaptation
  , ToDisplayFn(..)
    -- * Combinators
  , parens
  , brackets
  , braces
  , commaSep
  , spaceSep
    -- * Re-export HasDisplay
  , module TypedRedex.Logic.Display
  ) where

import Data.String (IsString(..))
import GHC.OverloadedLabels (IsLabel(..))
import GHC.TypeLits (KnownSymbol, symbolVal)
import Data.Proxy (Proxy(..))
import TypedRedex.Logic.Term (LogicType(..), Logic(..), Field(..))
import TypedRedex.Logic.Display

--------------------------------------------------------------------------------
-- Display Expression
--------------------------------------------------------------------------------

-- | Display expression: a template for rendering terms.
--
-- 'D' forms a Monoid under concatenation, with string literals
-- automatically lifted via OverloadedStrings.
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
-- #tArr ~> \\(a, b) -> a <+> " → " <+> b
-- @
--
-- Without '<+>', the literal " → " would be ambiguous between String and D.
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

-- | Wrap in braces
braces :: D -> D
braces d = "{" <> d <> "}"

-- | Comma-separated
commaSep :: [D] -> D
commaSep []     = Empty
commaSep [x]    = x
commaSep (x:xs) = x <> ", " <> commaSep xs

-- | Space-separated
spaceSep :: [D] -> D
spaceSep []     = Empty
spaceSep [x]    = x
spaceSep (x:xs) = x <> " " <> spaceSep xs

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
--   * Quaternary: @(D, D, D, D) -> D@
--   * Quinary: @(D, D, D, D, D) -> D@
--   * Senary: @(D, D, D, D, D, D) -> D@
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
  toDisplayFn _ _         = Lit "?"

-- Quaternary (tuple)
instance ToDisplayFn ((D, D, D, D) -> D) where
  toDisplayFn f (a:b:c:d:_) = f (a, b, c, d)
  toDisplayFn _ _           = Lit "?"

-- Quinary (tuple)
instance ToDisplayFn ((D, D, D, D, D) -> D) where
  toDisplayFn f (a:b:c:d:e:_) = f (a, b, c, d, e)
  toDisplayFn _ _             = Lit "?"

-- Senary (tuple)
instance ToDisplayFn ((D, D, D, D, D, D) -> D) where
  toDisplayFn f (a:b:c:d:e:g:_) = f (a, b, c, d, e, g)
  toDisplayFn _ _               = Lit "?"

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
-- #tArr ~> \\(a, b) -> a <+> " → " <+> b
-- @
(~>) :: ToDisplayFn f => Tag -> f -> DisplayRule a
(~>) (Tag name) f = DisplayRule name (toDisplayFn f)

infixr 0 ~>

-- | Variant for nullary constructors with explicit D type.
--
-- @
-- #tInt  ~= "int"
-- #tBool ~= "bool"
-- @
(~=) :: Tag -> D -> DisplayRule a
(~=) (Tag name) d = DisplayRule name (const d)

infixr 0 ~=

--------------------------------------------------------------------------------
-- Display Table
--------------------------------------------------------------------------------

-- | A display specification for type @a@: a list of rules.
newtype Display a = Display { unDisplay :: [DisplayRule a] }

-- | Create a display table from a list of rules.
--
-- @
-- tyDisplay :: Display Ty
-- tyDisplay = display
--   [ #tInt  ~= "int"
--   , #tArr  ~> \\(a, b) -> a <+> " → " <+> b
--   ]
-- @
display :: [DisplayRule a] -> Display a
display = Display

-- | Look up a display function by constructor name.
--
-- Returns the formatting function if found, or Nothing for fallback to default.
lookupDisplay :: String -> Display a -> Maybe ([D] -> D)
lookupDisplay name (Display rules) =
  case [ruleBody r | r <- rules, ruleName r == name] of
    (f:_) -> Just f
    []    -> Nothing

--------------------------------------------------------------------------------
-- Integration with TermFormatter
--------------------------------------------------------------------------------

-- | Format a term using the Display DSL.
--
-- This bridges the Display DSL with the existing formatting infrastructure.
-- Returns 'Just' the formatted string if a rule matches, 'Nothing' otherwise.
--
-- @
-- formatWithDisplay tyDisplay "TArr" ["int", "bool"]
--   == Just "int → bool"
-- @
formatWithDisplay :: Display a -> String -> [String] -> Maybe String
formatWithDisplay disp name args =
  case lookupDisplay name disp of
    Just f  -> Just $ renderD $ f (map Lit args)
    Nothing -> Nothing

--------------------------------------------------------------------------------
-- Rendering ground values and logic terms
--------------------------------------------------------------------------------

-- | Render a ground Haskell value using its HasDisplay instance.
--
-- This recursively renders nested types using their HasDisplay instances.
--
-- @
-- instance HasDisplay Env where
--   formatCon = formatWithDisplay envDisplay
--
-- renderGround (ETrm x ty EEmpty)  -- uses Env, Ty, Nom HasDisplay instances
-- @
renderGround :: forall a. (LogicType a, HasDisplay a) => a -> String
renderGround = renderReified . project
  where
    renderReified :: forall a' var. (LogicType a', HasDisplay a') => Reified a' var -> String
    renderReified r =
      let (name, fields) = quote r
          children = map renderFieldAny fields
      in case formatCon @a' name children of
           Just s  -> s
           Nothing -> defaultFormatCon name children

    renderFieldAny :: Field parent var -> String
    renderFieldAny (Field _ logic) = renderLogicAny logic

    renderLogicAny :: forall t var. (LogicType t, HasDisplay t) => Logic t var -> String
    renderLogicAny (Free _)    = "?"  -- shouldn't happen for ground values
    renderLogicAny (Ground r)  = renderReified r

-- | Render a logic term using HasDisplay instances.
--
-- Variables are rendered as "?", ground values use their display.
renderLogic :: forall a var. (LogicType a, HasDisplay a) => Logic a var -> String
renderLogic (Free _)   = "?"
renderLogic (Ground r) = renderReified r
  where
    renderReified :: forall a' var'. (LogicType a', HasDisplay a') => Reified a' var' -> String
    renderReified r' =
      let (name, fields) = quote r'
          children = map renderFieldAny fields
      in case formatCon @a' name children of
           Just s  -> s
           Nothing -> defaultFormatCon name children

    renderFieldAny :: Field parent var' -> String
    renderFieldAny (Field _ logic) = renderLogicAny logic

    renderLogicAny :: forall t var'. (LogicType t, HasDisplay t) => Logic t var' -> String
    renderLogicAny (Free _)   = "?"
    renderLogicAny (Ground r') = renderReified r'
