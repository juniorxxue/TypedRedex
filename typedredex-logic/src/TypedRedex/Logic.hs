-- | TypedRedex Logic - Core logic programming primitives.
--
-- This is the pure core layer with no presentation concerns.
-- It provides:
--
-- * 'Logic' – logic terms (variables or ground values)
-- * 'LogicType' – class for types that can be unified
-- * 'Redex' – class for logic programming interpreters
--
-- = Package Structure
--
-- @
-- typedredex-logic   (this package)
--       ↑
-- typedredex-dsl     (TH, smart constructors, Nominal)
--       ↑
-- typedredex-interp  (interpreters, pretty-printing)
-- @
module TypedRedex.Logic
  ( -- * Logic terms
    Logic(..)
  , Var(..)
  , LogicType(..)
  , Field(..)
    -- * Display
  , HasDisplay(..)
  , defaultFormatCon
    -- * Higher-rank helpers
  , Unifier
  , Evaluator
    -- * Interpreter classes
  , Redex(..)
  , RedexEval(..)
  , RedexNeg(..)
  , RedexStructure(..)
  , RedexFresh(..)
  , RedexHash(..)
  , EqVar(..)
    -- * Core types
  , Goal
  , Relation(..)
  , CapturedTerm(..)
  , FreshType(..)
  , CallType(..)
    -- * Nominal type classes
  , NominalAtom(..)
  , Permute(..)
  , Hash(..)
    -- * Unification helpers
  , flatteningUnify
  , occursCheck
  , evalFromRead
    -- * Substitution helpers
  , VarRepr
  , displayVarInt
    -- * Re-exports
  , Alternative(empty, (<|>))
  ) where

import TypedRedex.Logic.Term
import TypedRedex.Logic.Display
import TypedRedex.Logic.Redex
import TypedRedex.Logic.Unify
import TypedRedex.Logic.SubstCore
import TypedRedex.Logic.Nominal
