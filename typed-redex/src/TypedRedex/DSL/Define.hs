{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Clean DSL syntax for defining relations using inference-rule style.
--
-- This module provides a unified API for relations of any arity using
-- type-level lists.
--
-- @
-- lookupTm :: Redex rel => LTerm Ctx rel -> LTerm Nat rel -> LTerm Ty rel -> Applied rel '[Ctx, Nat, Ty]
-- lookupTm = judgment "lookupTm" [lookupTmHere, lookupTmThere, lookupTmSkip]
--   where
--     lookupTmHere = rule "lookup-here" $ fresh2 $ \\ty rest ->
--       concl $ lookupTm (tmBind ty rest) zro ty
--
--     lookupTmThere = rule "lookup-there" $ fresh4 $ \\ty ty' rest n' -> do
--       concl $ lookupTm (tmBind ty' rest) (suc n') ty
--       prem  $ lookupTm rest n' ty
-- @
--
-- Both 'concl' and 'prem' work for any arity.
-- Rule names are tracked for derivation trees.

module TypedRedex.DSL.Define
  ( -- * Type-level list of logic terms
    LTermList(..)
    -- * Applied relation type (unified for all arities)
  , Applied(..)
    -- * Judgment type alias (for concise signatures)
  , Judge
    -- * Conclusion and Premise (overloaded)
  , Conclude(..)
  , Premise(..)
    -- * Named rules (unified)
  , Rule(..)
  , rule
    -- * Judgment combinator (unified, works for all arities)
  , judgment
    -- * Type-level machinery
  , AllLogicType
  , Curried
  , CurriedR
    -- * Building helpers (for Moded DSL)
  , BuildLTermList(..)
  ) where

import TypedRedex.Core.Internal.Redex
import TypedRedex.Core.Internal.Logic
import TypedRedex.DSL.Fresh (LTerm, argument)
import TypedRedex.Core.Internal.Relation (call, (<=>))
import Control.Applicative (asum)
import Data.Kind (Type, Constraint)

--------------------------------------------------------------------------------
-- Type-level list of logic terms
--------------------------------------------------------------------------------

-- | Heterogeneous list of logic terms, indexed by a type-level list.
data LTermList rel (ts :: [Type]) where
  TNil  :: LTermList rel '[]
  (:>)  :: LogicType t => LTerm t rel -> LTermList rel ts -> LTermList rel (t ': ts)

infixr 5 :>

--------------------------------------------------------------------------------
-- Constraint family: all types in list must be LogicType
--------------------------------------------------------------------------------

-- | Constraint that all types in the list are LogicType instances.
type family AllLogicType (ts :: [Type]) :: Constraint where
  AllLogicType '[]       = ()
  AllLogicType (t ': ts) = (LogicType t, AllLogicType ts)

--------------------------------------------------------------------------------
-- Applied type: unified for all arities
--------------------------------------------------------------------------------

-- | Applied relation: stores arguments (as LTermList), goal, and judgment name.
-- Replaces Applied, Applied2, Applied3, Applied4, Applied5.
data Applied rel (ts :: [Type]) = Applied
  { appArgs :: LTermList rel ts
  , appGoal :: rel ()
  , appName :: String  -- ^ Judgment name (for deep interpretation markers)
  }

--------------------------------------------------------------------------------
-- Rule type: unified for all arities
--------------------------------------------------------------------------------

-- | A named rule for a judgment of any arity.
-- The type list ts determines the arity.
data Rule rel (ts :: [Type]) = Rule
  { ruleName :: String
  , ruleBody :: (?concl :: LTermList rel ts -> rel ()) => rel ()
  }

-- | Create a named rule. The name appears in derivation trees.
--
-- @
-- lookupHere = rule "lookup-here" $ fresh2 $ \\ty rest ->
--   concl $ lookup' (cons ty rest) zro ty
-- @
rule :: String -> ((?concl :: LTermList rel ts -> rel ()) => rel ()) -> Rule rel ts
rule name body = Rule name body

--------------------------------------------------------------------------------
-- Conclude: single instance for Applied rel ts
--------------------------------------------------------------------------------

-- | Type class for extracting conclusion pattern and unifying.
class Conclude app rel where
  type ConcludePat app
  concl :: (?concl :: ConcludePat app -> rel ()) => app -> rel ()

instance Redex rel => Conclude (Applied rel ts) rel where
  type ConcludePat (Applied rel ts) = LTermList rel ts
  concl (Applied args _ _) = do
    markConclusion  -- Emit marker for deep interpretation
    ?concl args

--------------------------------------------------------------------------------
-- Premise: single instance for Applied rel ts
--------------------------------------------------------------------------------

-- | Type class for running an applied relation as a premise.
class Premise app rel where
  prem :: app -> rel ()

instance Redex rel => Premise (Applied rel ts) rel where
  prem (Applied args g name) = do
    markPremise name (captureTerms args)  -- Emit marker for deep interpretation
    g

--------------------------------------------------------------------------------
-- Helper type classes for building judgment
--------------------------------------------------------------------------------

-- | Bind a list of arguments to fresh local variables.
class ArgumentList rel ts where
  argumentList :: LTermList rel ts -> (LTermList rel ts -> rel a) -> rel a

instance ArgumentList rel '[] where
  argumentList TNil f = f TNil

instance (Redex rel, LogicType t, ArgumentList rel ts) => ArgumentList rel (t ': ts) where
  argumentList (x :> xs) f = argument x $ \x' ->
    argumentList xs $ \xs' -> f (x' :> xs')

-- | Unify two LTermLists element-wise.
class UnifyList rel ts where
  unifyList :: LTermList rel ts -> LTermList rel ts -> rel ()

instance Redex rel => UnifyList rel '[] where
  unifyList TNil TNil = pure ()

instance (LogicType t, Redex rel, UnifyList rel ts) => UnifyList rel (t ': ts) where
  unifyList (x :> xs) (y :> ys) = (x <=> y) >> unifyList xs ys

-- | Capture terms from an LTermList for derivation tracking.
captureTerms :: LTermList rel ts -> [CapturedTerm rel]
captureTerms TNil = []
captureTerms (x :> xs) = CapturedTerm x : captureTerms xs

--------------------------------------------------------------------------------
-- Curried type family: compute curried function signature
--------------------------------------------------------------------------------

-- | Type family that computes the curried function type from a type list.
-- Curried rel '[A, B, C] = LTerm A rel -> LTerm B rel -> LTerm C rel -> Applied rel '[A, B, C]
type family Curried rel (ts :: [Type]) where
  Curried rel '[]       = Applied rel '[]
  Curried rel (t ': ts) = LTerm t rel -> Curried rel ts

-- | User-friendly type alias for judgment signatures.
--
-- @
-- -- Instead of writing:
-- substTyVar :: Redex rel => LTerm Nat rel -> LTerm Ty rel -> LTerm Nat rel -> LTerm Ty rel -> Applied rel '[Nat, Ty, Nat, Ty]
--
-- -- You can write:
-- substTyVar :: Redex rel => Judge rel '[Nat, Ty, Nat, Ty]
-- @
type Judge rel ts = CurriedR rel ts (Applied rel ts)

-- | Curried type with explicit result type (for internal use).
-- CurriedR rel '[A, B] r = LTerm A rel -> LTerm B rel -> r
type family CurriedR rel (ts :: [Type]) (r :: Type) where
  CurriedR rel '[]       r = r
  CurriedR rel (t ': ts) r = LTerm t rel -> CurriedR rel ts r

--------------------------------------------------------------------------------
-- BuildLTermList: helper for currying to LTermList
--------------------------------------------------------------------------------

-- | Helper class that converts curried arguments to an LTermList.
-- Uses continuation-passing style to build up the list.
class BuildLTermList rel ts where
  buildLTermList :: (LTermList rel ts -> r) -> CurriedR rel ts r

instance BuildLTermList rel '[] where
  buildLTermList f = f TNil

instance (LogicType t, BuildLTermList rel ts) => BuildLTermList rel (t ': ts) where
  buildLTermList f x = buildLTermList (\rest -> f (x :> rest))

--------------------------------------------------------------------------------
-- judgment: unified curried judgment combinator
--------------------------------------------------------------------------------

-- | Define a judgment from a list of named rules.
-- Works for any arity via type inference.
--
-- @
-- natLt :: Redex rel => LTerm Nat rel -> LTerm Nat rel -> Applied rel '[Nat, Nat]
-- natLt = judgment "natLt" [natLtZero, natLtSucc]
--   where
--     natLtZero = rule "lt-zero" $ fresh $ \\m' ->
--       concl $ natLt zro (suc m')
--
--     natLtSucc = rule "lt-succ" $ fresh2 $ \\n' m' -> do
--       concl $ natLt (suc n') (suc m')
--       prem  $ natLt n' m'
-- @
judgment :: forall rel ts. (BuildLTermList rel ts, Redex rel, ArgumentList rel ts, UnifyList rel ts)
         => String -> [Rule rel ts] -> CurriedR rel ts (Applied rel ts)
judgment name rules = buildLTermList $ \args ->
  let goal = argumentList args $ \args' ->
        let terms = captureTerms args
        in let ?concl = \pat -> unifyList args' pat
        in asum [call $ Relation (ruleName r) terms (ruleBody r) | r <- rules]
  in Applied args goal name  -- Store the judgment name
