{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Core types for defining relations using inference-rule style.
--
-- This module provides shared types used by the moded DSL and interpreters.
-- For user-facing API, use "TypedRedex.DSL.Moded".

module TypedRedex.DSL.Define
  ( -- * Type-level list of logic terms
    LTermList(..)
    -- * Applied relation type
  , Applied(..)
    -- * Constraint helper
  , AllLogicType
    -- * Building helpers (for Moded DSL)
  , BuildLTermList(..)
    -- * Type-level machinery
  , CurriedR
  ) where

import TypedRedex.Core.Internal.Redex (Redex(..), CapturedTerm(..))
import TypedRedex.Core.Internal.Logic (Logic(..), LogicType(..))
import TypedRedex.DSL.Fresh (LTerm, argument)
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
data Applied rel (ts :: [Type]) = Applied
  { appArgs :: LTermList rel ts
  , appGoal :: rel ()
  , appName :: String  -- ^ Judgment name (for deep interpretation markers)
  }

--------------------------------------------------------------------------------
-- Type families
--------------------------------------------------------------------------------

-- | Curried type with explicit result type (for internal use).
-- CurriedR rel '[A, B] r = LTerm A rel -> LTerm B rel -> r
type family CurriedR rel (ts :: [Type]) (r :: Type) where
  CurriedR rel '[]       r = r
  CurriedR rel (t ': ts) r = LTerm t rel -> CurriedR rel ts r

--------------------------------------------------------------------------------
-- Building LTermList from TArgs
--------------------------------------------------------------------------------

-- | Helper to capture all terms in an LTermList for derivation tracking
class CaptureTermsList rel ts where
  captureTermsList :: LTermList rel ts -> [CapturedTerm rel]

instance CaptureTermsList rel '[] where
  captureTermsList TNil = []

instance (LogicType t, CaptureTermsList rel ts) => CaptureTermsList rel (t ': ts) where
  captureTermsList (x :> xs) = CapturedTerm x : captureTermsList xs

-- | Convert LTermList to list of CapturedTerm (for derivation tracking)
captureTerms :: CaptureTermsList rel ts => LTermList rel ts -> [CapturedTerm rel]
captureTerms = captureTermsList

--------------------------------------------------------------------------------
-- Build LTermList (used by Moded.hs)
--------------------------------------------------------------------------------

-- | Build an LTermList from individual terms (used by moded DSL)
class BuildLTermList (ts :: [Type]) rel where
  buildLTermList :: BuildArgs ts rel -> LTermList rel ts

type family BuildArgs (ts :: [Type]) rel where
  BuildArgs '[] rel = ()
  BuildArgs '[t] rel = LTerm t rel
  BuildArgs '[t1, t2] rel = (LTerm t1 rel, LTerm t2 rel)
  BuildArgs '[t1, t2, t3] rel = (LTerm t1 rel, LTerm t2 rel, LTerm t3 rel)
  BuildArgs '[t1, t2, t3, t4] rel = (LTerm t1 rel, LTerm t2 rel, LTerm t3 rel, LTerm t4 rel)
  BuildArgs '[t1, t2, t3, t4, t5] rel = (LTerm t1 rel, LTerm t2 rel, LTerm t3 rel, LTerm t4 rel, LTerm t5 rel)

instance BuildLTermList '[] rel where
  buildLTermList () = TNil

instance LogicType t => BuildLTermList '[t] rel where
  buildLTermList x = x :> TNil

instance (LogicType t1, LogicType t2) => BuildLTermList '[t1, t2] rel where
  buildLTermList (x1, x2) = x1 :> x2 :> TNil

instance (LogicType t1, LogicType t2, LogicType t3) => BuildLTermList '[t1, t2, t3] rel where
  buildLTermList (x1, x2, x3) = x1 :> x2 :> x3 :> TNil

instance (LogicType t1, LogicType t2, LogicType t3, LogicType t4) => BuildLTermList '[t1, t2, t3, t4] rel where
  buildLTermList (x1, x2, x3, x4) = x1 :> x2 :> x3 :> x4 :> TNil

instance (LogicType t1, LogicType t2, LogicType t3, LogicType t4, LogicType t5) => BuildLTermList '[t1, t2, t3, t4, t5] rel where
  buildLTermList (x1, x2, x3, x4, x5) = x1 :> x2 :> x3 :> x4 :> x5 :> TNil
