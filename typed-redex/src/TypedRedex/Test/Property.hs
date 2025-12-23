{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Property-based testing for TypedRedex relations.
--
-- This module provides QuickCheck integration for testing properties of
-- relations. Relations are treated as blackbox functions: generate random
-- inputs, run the relation, and check properties on the outputs.
--
-- = Usage
--
-- @
-- -- 1. Derive Arbitrary for your syntax types
-- instance Arbitrary Ty where
--   arbitrary = ...
--
-- -- 2. Define a runner that converts your relation to a pure function
-- runSsub :: Env -> Env -> Ty -> Polar -> Ty -> Maybe Env
-- runSsub env senv ty1 p ty2 = listToMaybe $ takeS 1 $ ssubIO env senv ty1 p ty2
--
-- -- 3. Use propRel to test properties
-- prop_ssub_length :: Property
-- prop_ssub_length = propRel runSsub $ \\(env, senv, ty1, p, ty2) outEnv ->
--   envLength senv == envLength outEnv
-- @
module TypedRedex.Test.Property
  ( -- * Property combinators
    propRel
  , propRel2
  , propRel3
  , propRel4
  , propRel5
  , propRel6
    -- * Discarding invalid inputs
  , (==>?)
    -- * Re-exports from QuickCheck
  , Property
  , Arbitrary(..)
  , Gen
  , quickCheck
  , quickCheckWith
  , verboseCheck
  , Args(..)
  , stdArgs
  , forAll
  , (==>)
  , (.&&.)
  , (.||.)
  , counterexample
  , label
  , classify
  , collect
  , cover
  , oneof
  , frequency
  , elements
  , listOf
  , listOf1
  , vectorOf
  , sized
  , resize
  , scale
  , choose
  , chooseInt
  , suchThat
  , suchThatMaybe
  ) where

import Test.QuickCheck

-- | Test a property on a unary relation.
--
-- @
-- propRel runValue $ \\tm () -> isCanonical tm
-- @
propRel :: (Arbitrary a, Show a)
        => (a -> Maybe b)       -- ^ Relation runner (Nothing = no solution)
        -> (a -> b -> Bool)     -- ^ Property to check on (input, output)
        -> Property
propRel run prop = property $ \a ->
  case run a of
    Nothing -> discard
    Just b  -> prop a b

-- | Test a property on a binary relation.
propRel2 :: (Arbitrary a, Arbitrary b, Show a, Show b)
         => (a -> b -> Maybe c)
         -> ((a, b) -> c -> Bool)
         -> Property
propRel2 run prop = property $ \a b ->
  case run a b of
    Nothing -> discard
    Just c  -> prop (a, b) c

-- | Test a property on a ternary relation.
propRel3 :: (Arbitrary a, Arbitrary b, Arbitrary c, Show a, Show b, Show c)
         => (a -> b -> c -> Maybe d)
         -> ((a, b, c) -> d -> Bool)
         -> Property
propRel3 run prop = property $ \a b c ->
  case run a b c of
    Nothing -> discard
    Just d  -> prop (a, b, c) d

-- | Test a property on a 4-ary relation.
propRel4 :: (Arbitrary a, Arbitrary b, Arbitrary c, Arbitrary d,
             Show a, Show b, Show c, Show d)
         => (a -> b -> c -> d -> Maybe e)
         -> ((a, b, c, d) -> e -> Bool)
         -> Property
propRel4 run prop = property $ \a b c d ->
  case run a b c d of
    Nothing -> discard
    Just e  -> prop (a, b, c, d) e

-- | Test a property on a 5-ary relation.
propRel5 :: (Arbitrary a, Arbitrary b, Arbitrary c, Arbitrary d, Arbitrary e,
             Show a, Show b, Show c, Show d, Show e)
         => (a -> b -> c -> d -> e -> Maybe f)
         -> ((a, b, c, d, e) -> f -> Bool)
         -> Property
propRel5 run prop = property $ \a b c d e ->
  case run a b c d e of
    Nothing -> discard
    Just f  -> prop (a, b, c, d, e) f

-- | Test a property on a 6-ary relation.
--
-- This is the most common case for moded judgments with multiple inputs
-- and one output.
--
-- @
-- prop_ssub_length :: Property
-- prop_ssub_length = propRel6 runSsub $ \\(env, senv, ty1, p, ty2) outEnv ->
--   envLength senv == envLength outEnv
-- @
propRel6 :: (Arbitrary a, Arbitrary b, Arbitrary c, Arbitrary d, Arbitrary e,
             Arbitrary f, Show a, Show b, Show c, Show d, Show e, Show f)
         => (a -> b -> c -> d -> e -> f -> Maybe g)
         -> ((a, b, c, d, e, f) -> g -> Bool)
         -> Property
propRel6 run prop = property $ \a b c d e f ->
  case run a b c d e f of
    Nothing -> discard
    Just g  -> prop (a, b, c, d, e, f) g

-- | Conditional property with Maybe. Discards when condition is Nothing or False.
--
-- Useful for filtering inputs before running the relation.
--
-- @
-- propRel5 runSsub $ \\(env, senv, ty1, p, ty2) outEnv ->
--   wellFormed senv ==>? (envLength senv == envLength outEnv)
-- @
(==>?) :: Maybe Bool -> Bool -> Property
Nothing ==>? _ = discard
Just False ==>? _ = discard
Just True ==>? b = property b

infixr 0 ==>?
