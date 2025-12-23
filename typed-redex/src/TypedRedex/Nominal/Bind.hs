{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

-- | Binders with alpha-equivalence.
--
-- This module provides the 'Bind' type that represents binders with
-- built-in alpha-equivalence in unification. The 'Bind' type is
-- parameterized by the name type, allowing different kinds of binders.
--
-- @
-- Bind Nom Tm      -- term binder (lambda)
-- Bind TyNom Ty    -- type binder (forall)
-- Bind KindNom Ty  -- kind binder (if needed)
-- @
module TypedRedex.Nominal.Bind
  ( -- * Binder Type
    Bind(..)
    -- * Permutation (Name Swapping)
  , Permute(..)
    -- * Smart Constructor
  , mkBind
  , mkBindL
  ) where

import Control.Applicative (empty)
import Data.Proxy (Proxy(..))
import TypedRedex.Core.Internal.Logic
import TypedRedex.Interp.PrettyPrint (LogicVarNaming(..), VarNaming(..))
import TypedRedex.Nominal.Nom (NominalAtom(..))

--------------------------------------------------------------------------------
-- Permutation Typeclass
--------------------------------------------------------------------------------

-- | Typeclass for applying name permutations (swaps).
--
-- This is needed for alpha-equivalence: when unifying @Bind a t@ with @Bind b u@
-- where @a ≠ b@, we swap @a ↔ b@ in @u@ before unifying @t@ with the result.
class Permute name term where
  -- | Apply a swap: replace all occurrences of @a@ with @b@ and vice versa.
  swap :: name -> name -> term -> term

-- NominalAtom instances swap themselves
instance NominalAtom name => Permute name name where
  swap = swapAtom

-- Binders swap their components
instance (NominalAtom name, Permute name body) => Permute name (Bind name body) where
  swap a b (Bind n body) = Bind (swapAtom a b n) (swap a b body)

--------------------------------------------------------------------------------
-- Bind Type (Generic Binder)
--------------------------------------------------------------------------------

-- | A binder that binds a name in a body.
--
-- @Bind n body@ represents a term where @n@ is bound in @body@.
-- Alpha-equivalence: @Bind x (Var x) == Bind y (Var y)@ under unification.
--
-- The type is parameterized by:
-- - @name@: The type of nominal atom (e.g., 'Nom', 'TyNom')
-- - @body@: The type of the body
data Bind name body = Bind !name body
  deriving (Eq, Show)

instance LogicVarNaming (Bind name body) where
  varNaming = VarNaming "B" (\i -> "bnd" ++ show i)

instance (NominalAtom name, LogicType body, Permute name body) => LogicType (Bind name body) where
  data Reified (Bind name body) var = BindR (Logic name var) (Logic body var)

  project (Bind n b) = BindR (Ground (project n)) (Ground (project b))

  reify (BindR (Ground nr) (Ground br)) = Bind <$> reify nr <*> reify br
  reify _ = Nothing

  quote (BindR n b) = ("Bind", [Field (Proxy :: Proxy name) n, Field (Proxy :: Proxy body) b])

  -- Alpha-equivalence unification!
  unifyVal unif (BindR a1 b1) (BindR a2 b2) =
    case (a1, a2) of
      (Ground nr1, Ground nr2) ->
        case (reify nr1, reify nr2) of
          (Just n1, Just n2)
            | n1 == n2  -> unif b1 b2  -- Same name, unify bodies directly
            | otherwise ->
                -- Different names: apply alpha-equivalence
                case (b1, b2) of
                  (_, Ground br2) ->
                    -- b2 is ground: swap n1↔n2 in b2, then unify
                    case reify br2 of
                      Just body2 ->
                        let swapped = swap n1 n2 body2
                        in unif b1 (Ground (project swapped))
                      Nothing -> empty  -- Can't reify, fail
                  (Ground br1, Free _) ->
                    -- b1 is ground, b2 is Free: swap n2↔n1 in b1, then unify
                    case reify br1 of
                      Just body1 ->
                        let swapped = swap n2 n1 body1
                        in unif (Ground (project swapped)) b2
                      Nothing -> empty
                  (Free _, Free _) ->
                    -- Both are Free: just unify bodies directly
                    unif b1 b2
          _ -> empty  -- Can't reify names, fail
      _ ->
        -- At least one name is a logic variable
        unif a1 a2 *> unif b1 b2

  derefVal deref (BindR n b) = Bind <$> deref n <*> deref b

--------------------------------------------------------------------------------
-- Smart Constructor
--------------------------------------------------------------------------------

-- | Create a Bind logic term from a ground name and a (possibly variable) body.
--
-- @
-- mkBind x bodyVar  -- creates Bind x ?body where ?body is a logic variable
-- @
mkBind :: (NominalAtom name, LogicType body, Permute name body)
       => name -> Logic body var -> Logic (Bind name body) var
mkBind n body = Ground (BindR (Ground (project n)) body)

-- | Create a Bind logic term from two logic terms (name and body can both be variables).
--
-- @
-- mkBindL nameVar bodyVar  -- creates Bind ?name ?body where both are logic variables
-- @
mkBindL :: (NominalAtom name, LogicType name, LogicType body, Permute name body)
        => Logic name var -> Logic body var -> Logic (Bind name body) var
mkBindL nameL bodyL = Ground (BindR nameL bodyL)
