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
-- This module provides 'Bind' and 'TyBind' types that represent
-- binders with built-in alpha-equivalence in unification.
module TypedRedex.Nominal.Bind
  ( -- * Binder Types
    Bind(..)
  , TyBind(..)
    -- * Permutation (Name Swapping)
  , Permute(..)
    -- * Smart Constructors (work with logic variables)
  , mkBind
  , mkTyBind
  ) where

import Control.Applicative (empty)
import Data.Proxy (Proxy(..))
import TypedRedex.Core.Internal.Logic
import TypedRedex.Interp.PrettyPrint (LogicVarNaming(..), VarNaming(..))
import TypedRedex.Nominal.Nom

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

-- Nom swaps itself
instance Permute Nom Nom where
  swap a b x
    | x == a    = b
    | x == b    = a
    | otherwise = x

-- TyNom swaps itself
instance Permute TyNom TyNom where
  swap a b x
    | x == a    = b
    | x == b    = a
    | otherwise = x

-- Cross-namespace: Nom doesn't affect TyNom and vice versa
instance Permute Nom TyNom where
  swap _ _ x = x

instance Permute TyNom Nom where
  swap _ _ x = x

--------------------------------------------------------------------------------
-- Bind Type (Term Variable Binders)
--------------------------------------------------------------------------------

-- | A binder that binds a term variable name in a body.
--
-- @Bind x body@ represents a term where @x@ is bound in @body@.
-- Alpha-equivalence: @Bind x (Var x) == Bind y (Var y)@ under unification.
data Bind body = Bind !Nom body
  deriving (Eq, Show)

instance LogicVarNaming body => LogicVarNaming (Bind body) where
  varNaming = VarNaming "B" (\i -> "bnd" ++ show i)

instance (LogicType body, Permute Nom body) => LogicType (Bind body) where
  data Reified (Bind body) var = BindR (Logic Nom var) (Logic body var)

  project (Bind n b) = BindR (Ground (project n)) (Ground (project b))

  reify (BindR (Ground nr) (Ground br)) = Bind <$> reify nr <*> reify br
  reify _ = Nothing

  quote (BindR n b) =
    ( Constructor "Bind" $ \[Field _ n', Field _ b'] ->
        BindR (unsafeCoerceLogic n') (unsafeCoerceLogic b')
    , [Field (Proxy :: Proxy Nom) n, Field (Proxy :: Proxy body) b]
    )
    where
      -- This is safe because we know the types match
      unsafeCoerceLogic :: Logic a var -> Logic b var
      unsafeCoerceLogic (Free v) = error "unsafeCoerceLogic: Free"
      unsafeCoerceLogic (Ground _) = error "unsafeCoerceLogic: use pattern match"

  -- Alpha-equivalence unification!
  unifyVal unif (BindR a1 b1) (BindR a2 b2) =
    -- Try to reify both names to check if they're ground and what values they have
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
                    -- The names are internal fresh names from each rule
                    unif b1 b2
          _ -> empty  -- Can't reify names, fail
      _ ->
        -- At least one name is a logic variable
        unif a1 a2 *> unif b1 b2

  derefVal deref (BindR n b) = Bind <$> deref n <*> deref b

--------------------------------------------------------------------------------
-- TyBind Type (Type Variable Binders)
--------------------------------------------------------------------------------

-- | A binder that binds a type variable name in a body.
--
-- @TyBind α body@ represents a term/type where @α@ is bound in @body@.
data TyBind body = TyBind !TyNom body
  deriving (Eq, Show)

instance LogicVarNaming body => LogicVarNaming (TyBind body) where
  varNaming = VarNaming "TB" (\i -> "tybnd" ++ show i)

instance (LogicType body, Permute TyNom body) => LogicType (TyBind body) where
  data Reified (TyBind body) var = TyBindR (Logic TyNom var) (Logic body var)

  project (TyBind n b) = TyBindR (Ground (project n)) (Ground (project b))

  reify (TyBindR (Ground nr) (Ground br)) = TyBind <$> reify nr <*> reify br
  reify _ = Nothing

  quote (TyBindR n b) =
    ( Constructor "TyBind" $ \[Field _ n', Field _ b'] ->
        TyBindR (unsafeCoerceLogic n') (unsafeCoerceLogic b')
    , [Field (Proxy :: Proxy TyNom) n, Field (Proxy :: Proxy body) b]
    )
    where
      unsafeCoerceLogic :: Logic a var -> Logic b var
      unsafeCoerceLogic _ = error "unsafeCoerceLogic"

  -- Alpha-equivalence unification
  unifyVal unif (TyBindR a1 b1) (TyBindR a2 b2) =
    case (a1, a2) of
      (Ground nr1, Ground nr2) ->
        case (reify nr1, reify nr2) of
          (Just n1, Just n2)
            | n1 == n2  -> unif b1 b2
            | otherwise ->
                -- Different names: apply alpha-equivalence
                case (b1, b2) of
                  (_, Ground br2) ->
                    -- b2 is ground: swap n1↔n2 in b2, then unify
                    case reify br2 of
                      Just body2 ->
                        let swapped = swap n1 n2 body2
                        in unif b1 (Ground (project swapped))
                      Nothing -> empty
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
          _ -> empty
      _ ->
        unif a1 a2 *> unif b1 b2

  derefVal deref (TyBindR n b) = TyBind <$> deref n <*> deref b

--------------------------------------------------------------------------------
-- Smart Constructors (work with logic variables)
--------------------------------------------------------------------------------

-- | Create a Bind logic term from a ground name and a (possibly variable) body.
mkBind :: (LogicType body, Permute Nom body)
       => Nom -> Logic body var -> Logic (Bind body) var
mkBind n body = Ground (BindR (Ground (project n)) body)

-- | Create a TyBind logic term from a ground name and a (possibly variable) body.
mkTyBind :: (LogicType body, Permute TyNom body)
         => TyNom -> Logic body var -> Logic (TyBind body) var
mkTyBind n body = Ground (TyBindR (Ground (project n)) body)
