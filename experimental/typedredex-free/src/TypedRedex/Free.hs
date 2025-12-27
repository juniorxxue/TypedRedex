{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | TypedRedex Free - Indexed Free Monad DSL
--
-- This module provides a mode-checked DSL for defining logic programming
-- rules using indexed free monads.
--
-- = Architecture
--
-- @
--          IxFree (RuleF rel ts) s t a
--                     │
--    ┌────────────────┼────────────────┐
--    │                │                │
--    ▼                ▼                ▼
--  Eval           Typeset          Trace
-- (execute)    (extract rules)  (build derivations)
-- @
--
-- = Key Features
--
-- * **Pure AST**: Do-notation builds a pure data structure
-- * **Multiple Interpreters**: Same AST, different interpretations
-- * **Compile-Time Mode Checking**: Type families verify schedules
-- * **Automatic Reordering**: Premises executed in dependency order
--
-- = Usage
--
-- @
-- {-# LANGUAGE QualifiedDo, DataKinds, TypeApplications #-}
-- import qualified TypedRedex.Free as R
--
-- lookupCtx :: R.Judgment3 rel "lookup" '[R.I, R.I, R.O] Ctx Nat Ty
-- lookupCtx = R.defJudge3 \@"lookup" $ \\rule ->
--   [ rule "lookup-here" $ R.do
--       (ty, rest) <- R.fresh2
--       R.concl $ lookupCtx (cons ty rest) zro ty
--   ]
-- @
module TypedRedex.Free
  ( -- * Rule Monad
    RuleM
  , ModedRule(..)
  , ruleM
    -- * Smart Constructors
  , fresh, fresh2, fresh3, fresh4, fresh5, fresh6
  , concl
  , prem
  , neg
  , (===), (=/=)
  , liftRel
  , liftRelDeferred
    -- * Moded Terms
  , T(..)
  , ground
  , lift1, lift2, lift3
    -- * Argument Lists
  , TArgs(..)
  , ToLTermList(..)
  , LTermList(..)
    -- * Applied Judgments
  , AppliedM(..)
  , toApplied
    -- * Judgment Types
  , Judgment1, Judgment2, Judgment3, Judgment4, Judgment5, Judgment6
  , MJudgment1, MJudgment2, MJudgment3, MJudgment4, MJudgment5, MJudgment6
    -- * Judgment Helpers
  , mjudge1, mjudge2, mjudge3, mjudge4, mjudge5, mjudge6
  , defJudge1, defJudge2, defJudge3, defJudge4, defJudge5, defJudge6
    -- * Mode Types
  , Mode(..), ModeList(..), SingModeList(..)
  , In, Out, GetMode, GetType
    -- * Schedule Checking
  , CheckSchedule
  , Union
    -- * QualifiedDo Support
  , return, (>>=), (>>)
    -- * Re-exports from Logic
  , LogicType(..), Logic(..), Field(..)
  , Redex(..), RedexNeg
  ) where

import Prelude hiding (return, (>>=), (>>))

import TypedRedex.Free.Moded
import TypedRedex.Free.Schedule (Mode(..), ModeList(..), SingModeList(..), CheckSchedule, Union)
import TypedRedex.Logic (LogicType(..), Logic(..), Field(..), Redex(..), RedexNeg)
