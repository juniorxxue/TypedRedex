{-# LANGUAGE TypeFamilies, GADTs, DataKinds, RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE PatternSynonyms, ViewPatterns #-}

-- | HKD-based core for TypedRedex.
--
-- Key idea: AST functors like @TyF@ are parameterized by child type.
-- - Plain values: @Fix TyF@
-- - Logic terms: @Term TyF@
--
-- Same constructors (TInt, TArr) work for both!
module HKT.Core
  ( -- * Variables
    VarId(..)
    -- * Logic terms
  , Term(..)
  , pattern Var
  , pattern Con
    -- * Plain recursive types
  , Fix(..)
    -- * Type classes
  , HKT(..)
    -- * Smart constructors
  , var
  , con
    -- * Utilities
  , children
  ) where

import Data.Kind (Type)

--------------------------------------------------------------------------------
-- Variables
--------------------------------------------------------------------------------

newtype VarId = VarId Int
  deriving (Eq, Ord, Show)

--------------------------------------------------------------------------------
-- Logic Terms
--------------------------------------------------------------------------------

-- | A logic term: either a variable or a constructor.
--
-- @f@ is the "base functor" (e.g., TyF, ExprF).
-- Children of constructors are themselves @Term f@.
data Term (f :: Type -> Type) where
  Var_ :: VarId -> Term f
  Con_ :: f (Term f) -> Term f

-- Pattern synonyms for nicer API
pattern Var :: VarId -> Term f
pattern Var v = Var_ v

pattern Con :: f (Term f) -> Term f
pattern Con x = Con_ x

{-# COMPLETE Var, Con #-}

instance (forall a. Show a => Show (f a)) => Show (Term f) where
  showsPrec p (Var (VarId n)) = showParen (p > 10) $ showString "Var " . shows n
  showsPrec p (Con x) = showParen (p > 10) $ showString "Con " . showsPrec 11 x

--------------------------------------------------------------------------------
-- Plain Recursive Types
--------------------------------------------------------------------------------

-- | Fixpoint for plain recursive types.
newtype Fix f = Fix { unFix :: f (Fix f) }

instance (forall a. Show a => Show (f a)) => Show (Fix f) where
  showsPrec p (Fix x) = showsPrec p x

--------------------------------------------------------------------------------
-- HKT Class
--------------------------------------------------------------------------------

-- | Types that can be used in logic programming.
--
-- @F a@ is the base functor for type @a@.
class (Functor (F a), Foldable (F a)) => HKT a where
  type F a :: Type -> Type

-- | Smart constructor: wrap a functor value as a logic term.
con :: f (Term f) -> Term f
con = Con

-- | Smart constructor: create a variable term.
var :: VarId -> Term f
var = Var

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

-- | Get all child terms from a constructor.
children :: Foldable f => Term f -> [Term f]
children (Var _) = []
children (Con x) = foldr (:) [] x
