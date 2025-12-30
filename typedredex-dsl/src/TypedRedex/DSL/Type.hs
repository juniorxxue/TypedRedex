{-# LANGUAGE Rank2Types #-}

-- | Type-level helpers for defining LogicType instances.
--
-- This module provides utilities for defining custom types that can be
-- used in logic programs.
module TypedRedex.DSL.Type
( field
, quote0, quote1, quote2, quote3
, LogicType(quote, unifyVal, derefVal)
, empty
) where

import Data.Proxy (Proxy(Proxy))
import TypedRedex.Logic
import Control.Applicative (Alternative (empty))

-- | Wrap a logic term as a field for quote.
field :: (LogicType t, HasDisplay t) => Logic t var -> Field a var
field x = Field Proxy x

-- | Quote a nullary constructor.
quote0 :: String -> (String, [Field t v])
quote0 c = (c, [])

-- | Quote a unary constructor.
quote1 :: (LogicType a, HasDisplay a) => String -> Logic a v -> (String, [Field t v])
quote1 c x = (c, [field x])

-- | Quote a binary constructor.
quote2 :: (LogicType a, HasDisplay a, LogicType b, HasDisplay b) => String -> Logic a v -> Logic b v -> (String, [Field t v])
quote2 c x y = (c, [field x, field y])

-- | Quote a ternary constructor.
quote3 :: (LogicType a, HasDisplay a, LogicType b, HasDisplay b, LogicType c, HasDisplay c) => String -> Logic a v -> Logic b v -> Logic c v -> (String, [Field t v])
quote3 c x y z = (c, [field x, field y, field z])
