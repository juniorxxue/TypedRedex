{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Prelude for nominal logic with standard name types.
--
-- This module provides convenience types and functions for common use cases:
--
-- @
-- import TypedRedex
-- import TypedRedex.Nominal
-- import TypedRedex.Nominal.Prelude  -- for Nom, TyNom, freshNom, etc.
--
-- data Tm = Var Nom | Lam Ty (Bind Nom Tm) | App Tm Tm
--
-- -- In rules, you can mix logic variables and nominal atoms:
-- fresh5 $ \\ctx tyA x body tyB -> do
--   -- ctx :: LTerm Ctx rel, x :: Nom, body :: LTerm Tm rel
--   concl $ typeof ctx (lam tyA (bind x body)) (tarr tyA tyB)
-- @
--
-- For custom name types, use 'TypedRedex.Nominal' directly with 'RedexFresh'.
module TypedRedex.Nominal.Prelude
  ( -- * Standard Name Types
    Nom(..)
  , TyNom(..)
    -- * Fresh Name Generation
  , FreshName(..)
  , freshNom
  , freshTyNom
  , freshNom_
  , freshTyNom_
    -- * Convenience Unbind
  , unbind
  , unbindTy
  , unbind2
  , unbind2With
    -- * Smart Constructors
  , nom
  , tynom
  ) where

import Control.Applicative (empty)
import TypedRedex.Logic
import TypedRedex.DSL.Fresh (LTerm, Freshable(..))
import TypedRedex.DSL.Eval (eval)
import TypedRedex.Nominal.Nom (NominalAtom(..))
import TypedRedex.Nominal.Bind (Bind(..), Permute(..), mkBind)
import TypedRedex.Nominal.Hash (Hash(..))

--------------------------------------------------------------------------------
-- Nominal Atom Types
--------------------------------------------------------------------------------

-- | A nominal atom for term variables.
--
-- Nom values are ground identifiers that represent variable names.
-- Two Noms are equal iff they have the same index.
newtype Nom = Nom { nomId :: Int }
  deriving (Eq, Ord)

instance Show Nom where
  show (Nom n) = "x" ++ show n

instance NominalAtom Nom

-- | A nominal atom for type variables.
--
-- TyNom values are ground identifiers that represent type variable names.
newtype TyNom = TyNom { tyNomId :: Int }
  deriving (Eq, Ord)

instance Show TyNom where
  show (TyNom n) = "α" ++ show n

instance NominalAtom TyNom

-- | Default display for Nom (shows as variable name)
instance HasDisplay Nom where
  formatCon "Nom" [n] = Just $ "x" ++ n
  formatCon _ _ = Nothing

-- | Default display for TyNom (shows as type variable name)
instance HasDisplay TyNom where
  formatCon "TyNom" [n] = Just $ "α" ++ n
  formatCon _ _ = Nothing

--------------------------------------------------------------------------------
-- LogicType Instances
--------------------------------------------------------------------------------

-- | LogicType instance for Int (primitive type).
instance LogicType Int where
  data Reified Int var = IntR Int

  project n = IntR n

  reify (IntR n) = Just n

  children (IntR _) = []

  quote (IntR n) = (show n, [])

  unifyVal _ (IntR a) (IntR b)
    | a == b    = pure ()
    | otherwise = empty

  derefVal _ (IntR n) = pure n

instance HasDisplay Int where
  formatCon name [] = Just name  -- Already formatted as number string
  formatCon _ _ = Nothing

instance LogicType Nom where
  data Reified Nom var = NomR Int

  project (Nom n) = NomR n

  reify (NomR n) = Just (Nom n)

  children (NomR _) = []

  unifyVal _ (NomR a) (NomR b)
    | a == b    = pure ()
    | otherwise = empty

  derefVal _ (NomR n) = pure (Nom n)


instance LogicType TyNom where
  data Reified TyNom var = TyNomR Int

  project (TyNom n) = TyNomR n

  reify (TyNomR n) = Just (TyNom n)

  children (TyNomR _) = []

  unifyVal _ (TyNomR a) (TyNomR b)
    | a == b    = pure ()
    | otherwise = empty

  derefVal _ (TyNomR n) = pure (TyNom n)

--------------------------------------------------------------------------------
-- Cross-namespace Permute instances
--------------------------------------------------------------------------------

-- Swapping Nom doesn't affect TyNom
instance Permute Nom TyNom where
  swap _ _ x = x

-- Swapping TyNom doesn't affect Nom
instance Permute TyNom Nom where
  swap _ _ x = x

-- Swapping Nom doesn't affect Int
instance Permute Nom Int where
  swap _ _ x = x

-- Swapping TyNom doesn't affect Int
instance Permute TyNom Int where
  swap _ _ x = x

--------------------------------------------------------------------------------
-- Cross-namespace Hash instances
--------------------------------------------------------------------------------

-- Nom never occurs free in TyNom (different namespaces)
instance Hash Nom TyNom where
  occursIn _ _ = False

-- TyNom never occurs free in Nom
instance Hash TyNom Nom where
  occursIn _ _ = False

-- Names never occur in Int (primitive type)
instance Hash Nom Int where
  occursIn _ _ = False

instance Hash TyNom Int where
  occursIn _ _ = False

--------------------------------------------------------------------------------
-- Fresh Name Generation
--------------------------------------------------------------------------------

-- | Generate a fresh term variable name.
freshNom :: RedexFresh rel => rel Nom
freshNom = Nom <$> freshInt

-- | Generate a fresh type variable name.
freshTyNom :: RedexFresh rel => rel TyNom
freshTyNom = TyNom <$> freshInt

-- | CPS version of 'freshNom'.
freshNom_ :: RedexFresh rel => (Nom -> rel a) -> rel a
freshNom_ k = freshNom >>= k

-- | CPS version of 'freshTyNom'.
freshTyNom_ :: RedexFresh rel => (TyNom -> rel a) -> rel a
freshTyNom_ k = freshTyNom >>= k

--------------------------------------------------------------------------------
-- FreshName Typeclass
--------------------------------------------------------------------------------

-- | Typeclass for generating fresh names, abstracting over name types.
--
-- This allows generic functions like 'unbind' and 'unbind2' to work with
-- any nominal atom type without requiring separate implementations.
class NominalAtom name => FreshName name where
  freshName_ :: RedexFresh rel => (name -> rel a) -> rel a

instance FreshName Nom where
  freshName_ = freshNom_

instance FreshName TyNom where
  freshName_ = freshTyNom_

--------------------------------------------------------------------------------
-- Freshable instances (for unified fresh)
--------------------------------------------------------------------------------

-- | Nom can be freshly allocated in any relation that supports RedexFresh.
instance RedexFresh rel => Freshable Nom rel where
  freshOne k = freshNom >>= k

-- | TyNom can be freshly allocated in any relation that supports RedexFresh.
instance RedexFresh rel => Freshable TyNom rel where
  freshOne k = freshTyNom >>= k

--------------------------------------------------------------------------------
-- Convenience Unbind
--------------------------------------------------------------------------------

-- | Open a binder with a fresh name (generic over name type).
--
-- The type of the 'Bind' determines which 'FreshName' instance to use.
unbind :: (RedexFresh rel, RedexEval rel, FreshName name,
           LogicType body, Permute name body,
           HasDisplay name, HasDisplay body)
       => LTerm (Bind name body) rel
       -> rel (LTerm name rel, LTerm body rel)
unbind bndL = do
  Bind oldName body <- eval bndL
  freshName_ $ \fresh -> do
    let swappedBody = swap oldName fresh body
    pure (Ground (project fresh), Ground (project swappedBody))

-- | Open a term binder (Bind Nom) with a fresh name.
-- Specialized version of 'unbind' for term variables.
unbindTy :: (RedexFresh rel, RedexEval rel, LogicType body, Permute TyNom body, HasDisplay body)
         => LTerm (Bind TyNom body) rel
         -> rel (LTerm TyNom rel, LTerm body rel)
unbindTy = unbind

-- | Open two binders with the SAME fresh name (generic version).
--
-- Takes a fresh name generator as the first argument.
-- Use this when you need a custom fresh generator.
unbind2With :: (RedexEval rel, NominalAtom name,
                LogicType body1, LogicType body2,
                Permute name body1, Permute name body2,
                HasDisplay name, HasDisplay body1, HasDisplay body2)
            => (forall a. (name -> rel a) -> rel a)
            -> LTerm (Bind name body1) rel
            -> LTerm (Bind name body2) rel
            -> rel (LTerm name rel, LTerm body1 rel, LTerm body2 rel)
unbind2With freshGen bnd1L bnd2L = do
  Bind n1 body1 <- eval bnd1L
  Bind n2 body2 <- eval bnd2L
  freshGen $ \fresh -> do
    let swapped1 = swap n1 fresh body1
        swapped2 = swap n2 fresh body2
    pure (Ground (project fresh), Ground (project swapped1), Ground (project swapped2))

-- | Open two binders with the SAME fresh name.
--
-- Essential for rules comparing ∀-types (subtyping, equivalence)
-- where both bodies must refer to the same bound variable.
--
-- @
-- rule "forall" $ do
--     (bd1, bd2) <- fresh2
--     (a, tyA, tyB) <- unbind2 bd1 bd2  -- Opens both with same fresh name
--     prem  $ ssub (euvar a env1) tyA p tyB (euvar a env2)
--     concl $ ssub env1 (tforall bd1) p (tforall bd2) env2
-- @
unbind2 :: (RedexFresh rel, RedexEval rel, FreshName name,
            LogicType body1, LogicType body2,
            Permute name body1, Permute name body2,
            HasDisplay name, HasDisplay body1, HasDisplay body2)
        => LTerm (Bind name body1) rel
        -> LTerm (Bind name body2) rel
        -> rel (LTerm name rel, LTerm body1 rel, LTerm body2 rel)
unbind2 = unbind2With freshName_

--------------------------------------------------------------------------------
-- Smart Constructors
--------------------------------------------------------------------------------

-- | Create a ground term variable reference.
nom :: Nom -> LTerm Nom rel
nom = Ground . project

-- | Create a ground type variable reference.
tynom :: TyNom -> LTerm TyNom rel
tynom = Ground . project
