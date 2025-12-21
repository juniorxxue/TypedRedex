{-# LANGUAGE Rank2Types, LambdaCase, ApplicativeDo #-}

-- | Type-level helpers for defining LogicType instances.
--
-- This module provides utilities for defining custom types that can be
-- used in logic programs.
module TypedRedex.DSL.Type
(
  defaultUnif
, field
, con0, con1, con2, con3
, quote0, quote1, quote2, quote3
, LogicType(quote, unifyVal, derefVal)
, LogicVarNaming
, empty
) where

import Data.Proxy (Proxy(Proxy))
import TypedRedex.Core.Internal.Logic
import TypedRedex.Interp.PrettyPrint (LogicVarNaming)
import Text.Printf (printf)
import Unsafe.Coerce (unsafeCoerce)
import Control.Applicative (Alternative (empty))
import Control.Monad (guard)
import Data.Foldable (traverse_)

defaultUnif :: (Alternative rel, LogicType a) => Unifier rel var -> Reified a var -> Reified a var -> rel ()
defaultUnif unif x y = do
    let (con_x, xs) = quote x
    let (con_y, ys) = quote y
    guard (constructorName con_x == constructorName con_y)
    traverse_ (\((Field _ xi), (Field _ yi)) -> unif xi (unsafeCoerce yi)) (zip xs ys)
    pure ()

field :: LogicType t => Logic t var -> Field a var
field x = Field Proxy x

reifyError :: String -> Int -> [x] -> a
reifyError con expected actual = error $ printf "Constructor %s expected %d fields, got %d" con expected (length actual)

con0 :: String -> (forall var. Reified t var) -> Constructor t
con0 c r = Constructor c $ \case
    [] -> r
    xs -> reifyError c 0 xs

con1 :: String -> (forall var. Logic a var -> Reified t var) -> Constructor t
con1 c r = Constructor c $ \case
    [Field _ x] -> r (unsafeCoerce x)
    xs -> reifyError c 1 xs

con2 :: String -> (forall var. Logic a var -> Logic b var -> Reified t var) -> Constructor t
con2 c r = Constructor c $ \case
    [Field _ x, Field _ y] -> r (unsafeCoerce x) (unsafeCoerce y)
    xs -> reifyError c 2 xs

con3 :: String -> (forall var. Logic a var -> Logic b var -> Logic c var -> Reified t var) -> Constructor t
con3 c r = Constructor c $ \case
    [Field _ x, Field _ y, Field _ z] -> r (unsafeCoerce x) (unsafeCoerce y) (unsafeCoerce z)
    xs -> reifyError c 3 xs

quote0 :: String -> (forall var. Reified t var) -> (Constructor t, [Field t v])
quote0 c r = (con0 c r, [])

quote1 :: LogicType a => String -> (forall var. Logic a var -> Reified t var) -> Logic a v -> (Constructor t, [Field t v])
quote1 c r x = (con1 c r, [field x])

quote2 :: (LogicType a, LogicType b) => String -> (forall var. Logic a var -> Logic b var -> Reified t var) -> Logic a v -> Logic b v -> (Constructor t, [Field t v])
quote2 c r x y = (con2 c r, [field x, field y])

quote3 :: (LogicType a, LogicType b, LogicType c) => String -> (forall var. Logic a var -> Logic b var -> Logic c var -> Reified t var) -> Logic a v -> Logic b v -> Logic c v -> (Constructor t, [Field t v])
quote3 c r x y z = (con3 c r, [field x, field y, field z])
