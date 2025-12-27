{-# LANGUAGE TypeFamilies, DataKinds #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

-- | STLC Syntax - HKD style
--
-- Key insight: Smart constructors work on @T vs f@, not @Term f@.
-- This enables type inference without explicit type applications.
module HKT.Example.Syntax
  ( -- * Types
    TyF(..)
  , tunit, tarr
    -- * Expressions
  , ExprF(..)
  , evar, eunit, elam, eapp, eann
    -- * Contexts
  , CtxF(..)
  , cnil, ccons
    -- * Re-exports
  , T(..), ground, Term(..), VarId(..)
  ) where

import qualified Data.Set as S

import HKT.Core
import HKT.Moded (T(..), ground, Union)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

data TyF r
  = TUnit
  | TArr r r
  deriving (Eq, Show, Functor, Foldable, Traversable)

-- Smart constructors on T (not Term!)
-- This enables type inference: tarr a b constrains a,b to T _ TyF

tunit :: T '[] TyF
tunit = ground (Con TUnit)

tarr :: T vs1 TyF -> T vs2 TyF -> T (Union vs1 vs2) TyF
tarr (T v1 t1) (T v2 t2) = T (S.union v1 v2) (Con (TArr t1 t2))

--------------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------------

data ExprF r
  = EVar Int        -- de Bruijn index
  | EUnit           -- unit value
  | ELam r          -- λ.e (body)
  | EApp r r        -- e₁ e₂
  | EAnn r (Term TyF)  -- (e : A)
  deriving (Functor, Foldable, Traversable)

evar :: Int -> T '[] ExprF
evar n = ground (Con (EVar n))

eunit :: T '[] ExprF
eunit = ground (Con EUnit)

elam :: T vs ExprF -> T vs ExprF
elam (T v t) = T v (Con (ELam t))

eapp :: T vs1 ExprF -> T vs2 ExprF -> T (Union vs1 vs2) ExprF
eapp (T v1 t1) (T v2 t2) = T (S.union v1 v2) (Con (EApp t1 t2))

eann :: T vs1 ExprF -> T vs2 TyF -> T (Union vs1 vs2) ExprF
eann (T v1 t1) (T v2 t2) = T (S.union v1 v2) (Con (EAnn t1 t2))

--------------------------------------------------------------------------------
-- Contexts
--------------------------------------------------------------------------------

data CtxF r
  = CNil
  | CCons (Term TyF) r
  deriving (Functor, Foldable, Traversable)

cnil :: T '[] CtxF
cnil = ground (Con CNil)

ccons :: T vs1 TyF -> T vs2 CtxF -> T (Union vs1 vs2) CtxF
ccons (T v1 t1) (T v2 t2) = T (S.union v1 v2) (Con (CCons t1 t2))
