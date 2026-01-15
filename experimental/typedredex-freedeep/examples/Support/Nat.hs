{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Support.Nat
  ( Nat(..)
  , zro
  , suc
  ) where

import TypedRedex.Core.Term
import TypedRedex.Pretty

-- | Natural numbers.
data Nat = Z | S Nat
  deriving (Eq, Show)

instance Repr Nat where
  data Reified Nat = RZ | RS (Logic Nat)

  project Z     = RZ
  project (S n) = RS (Ground (project n))

  reify RZ = Just Z
  reify (RS (Ground r)) = S <$> reify r
  reify _ = Nothing

  quote RZ     = ("Z", [])
  quote (RS n) = ("S", [Field n])

  mapReified _ RZ = RZ
  mapReified f (RS n) = RS (f n)

instance Pretty Nat where
  varNames = cycleNames ["n", "m", "k"]

  prettyReified RZ = pure (text "0")
  prettyReified (RS n) = do
    d <- prettyLogic n
    pure (text "S(" <+> d <+> text ")")

-- | Smart constructors.
zro :: Term '[] Nat
zro = ground Z

suc :: Term vs Nat -> Term vs Nat
suc = lift1 (\n -> Ground (RS n))
