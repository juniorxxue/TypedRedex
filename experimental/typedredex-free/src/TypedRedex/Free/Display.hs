{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Display DSL for defining how to pretty-print logic types.
--
-- This module allows users to write display rules using familiar
-- pattern-matching syntax on the original type, without knowing
-- about the internal 'Reified' representation.
--
-- = Example Usage
--
-- @
-- -- Original type
-- data Tm = Var Nat | Unit | Lam Tm | App Tm Tm | Ann Tm Ty
--
-- -- Display rules using pattern synonyms
-- tmDisplay :: Pat Tm -> D
-- tmDisplay = \\case
--   Var_ n     -> "var " <> n
--   Unit_      -> "()"
--   Lam_ b     -> "λ. " <> b
--   App_ f x   -> f <> " " <> x
--   Ann_ e t   -> e <> " : " <> t
--
-- -- Convert to ShowReified instance
-- instance ShowReified Tm where
--   showReified = fromDisplay tmDisplay
-- @
module TypedRedex.Free.Display
  ( -- * Display Expression
    D(..)
  , renderD
    -- * Pattern Type
  , Pat(..)
  , matchPat
    -- * Building Display Rules
  , DisplayRules(..)
  , displayRules
  , fromDisplay
    -- * Combinators
  , parens
  , brackets
  , braces
  , sep
  , commaSep
    -- * For TH-generated pattern synonyms
  , mkPat
  ) where

import Data.String (IsString(..))
import Data.Typeable (Typeable, TypeRep, typeRep)
import Data.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- Display Expression
--------------------------------------------------------------------------------

-- | A display expression: a template for rendering terms.
--
-- 'D' forms a Monoid under concatenation, with string literals
-- automatically lifted via OverloadedStrings.
data D
  = Lit String           -- ^ Literal text
  | Child Int TypeRep    -- ^ Reference to child at index, with type info
  | Seq D D              -- ^ Concatenation
  | Parens D             -- ^ Parenthesized
  | Empty                -- ^ Empty
  deriving (Show, Eq)

instance IsString D where
  fromString = Lit

instance Semigroup D where
  Empty <> y = y
  x <> Empty = x
  x <> y     = Seq x y

instance Monoid D where
  mempty = Empty

-- | Wrap in parentheses
parens :: D -> D
parens = Parens

-- | Wrap in brackets
brackets :: D -> D
brackets d = "[" <> d <> "]"

-- | Wrap in braces
braces :: D -> D
braces d = "{" <> d <> "}"

-- | Separate with a delimiter
sep :: D -> [D] -> D
sep _ []     = Empty
sep _ [x]    = x
sep s (x:xs) = x <> s <> sep s xs

-- | Comma-separated
commaSep :: [D] -> D
commaSep = sep ", "

-- | Render a display expression given a function to render children.
renderD :: (Int -> String) -> D -> String
renderD _     (Lit s)       = s
renderD child (Child i _)   = child i
renderD child (Seq a b)     = renderD child a ++ renderD child b
renderD child (Parens d)    = "(" ++ renderD child d ++ ")"
renderD _     Empty         = ""

--------------------------------------------------------------------------------
-- Pattern Type for Matching
--------------------------------------------------------------------------------

-- | A pattern for matching constructors of type @a@.
--
-- This captures the constructor name and its children as 'D' placeholders,
-- allowing users to write pattern matches that look like the original type.
data Pat a = Pat
  { patCon      :: String    -- ^ Constructor name
  , patChildren :: [D]       -- ^ Children as display placeholders
  }
  deriving (Show, Eq)

-- | Create a pattern with the given constructor name and arity.
--
-- This is used by TH-generated pattern synonyms.
mkPat :: forall a. Typeable a => String -> Int -> Pat a
mkPat con arity = Pat con [Child i (typeRep (Proxy @a)) | i <- [0..arity-1]]

-- | Match a pattern and extract the display function.
--
-- Used internally to convert pattern match results.
matchPat :: Pat a -> (String, [D])
matchPat (Pat con children) = (con, children)

--------------------------------------------------------------------------------
-- Display Rules
--------------------------------------------------------------------------------

-- | Display rules for a type: a function from patterns to display expressions.
newtype DisplayRules a = DisplayRules
  { unDisplayRules :: Pat a -> D
  }

-- | Create display rules from a pattern-matching function.
--
-- @
-- tmDisplay :: DisplayRules Tm
-- tmDisplay = displayRules $ \\case
--   Var_ n     -> "var " <> n
--   Unit_      -> "()"
--   Lam_ b     -> "λ. " <> b
--   App_ f x   -> f <> " " <> x
--   Ann_ e t   -> e <> " : " <> t
-- @
displayRules :: (Pat a -> D) -> DisplayRules a
displayRules = DisplayRules

-- | Convert display rules to a 'showReified'-compatible function.
--
-- This is the bridge between the user-facing DSL and the internal
-- 'ShowReified' class.
--
-- @
-- instance ShowReified Tm where
--   showReified = fromDisplay tmDisplay tmPatterns
-- @
fromDisplay :: forall a var.
               DisplayRules a                              -- ^ User's display rules
            -> (forall r. (String -> [D] -> r) -> a -> r)  -- ^ Pattern extractor
            -> (forall t. Logic t var -> String)           -- ^ Child renderer
            -> Reified a var                               -- ^ Value to display
            -> String
fromDisplay rules extract showChild reified =
  let -- Extract constructor and children from Reified
      -- This uses the pattern extractor to get (conName, children as D)
      -- Then we build a Pat and apply the rules
      result = undefined -- placeholder, actual impl depends on Reified structure
  in result

--------------------------------------------------------------------------------
-- Re-exports for convenience
--------------------------------------------------------------------------------

-- These are needed for the DSL to work with OverloadedStrings
-- and pattern matching.

-- | Logic term (re-exported for display functions)
data Logic a var
  = Free (Var a var)
  | Ground (Reified a var)

-- | Placeholder - actual definition in TypedRedex.Logic
data Var a var = Var

-- | Placeholder - actual definition in LogicRepr
data family Reified a var
