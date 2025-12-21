{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RebindableSyntax #-}

-- | Test static checking of negation-as-failure.
--
-- GOOD example compiles, BAD example (when uncommented) shows compile error.
module NegRules where

import Prelude hiding ((>>=), (>>), return)
import TypedRedex hiding (fresh, fresh2, fresh3, fresh4, fresh5, fresh6, ground, lift1, lift2, lift3, neg)
import TypedRedex.DSL.Moded
  ( Mode(..), T(..), Union
  , AppliedM(..), defJudge2, ModedRule(..)
  , fresh, fresh2, fresh3, prem, concl, neg, ground, lift2
  , return, (>>=), (>>)
  )

-- Import types from stlc-bidir
import Rules (Nat(..), Ctx(..), Ty(..), lookupCtx, zro, suc, nil, cons)

--------------------------------------------------------------------------------
-- GOOD: notInCtx2 - all variables grounded before negation
-- This should compile successfully
--------------------------------------------------------------------------------

-- | Check that index n is NOT in context ctx.
-- Uses negation-as-failure with ALL variables grounded.
notInCtx2 :: (RedexNeg rel, LogicType Ctx, LogicType Nat, LogicType Ty)
          => T vs1 Ctx rel -> T vs2 Nat rel
          -> AppliedM rel "notInCtx2" '[I, I] '[vs1, vs2] '[Ctx, Nat]
notInCtx2 = defJudge2 @"notInCtx2" $ \rule ->
  [ rule "not-in-empty" $ do
      n <- fresh
      concl $ notInCtx2 nil n
      -- Empty context: any index is not in it (no negation needed, just base case)

  , rule "not-in-cons" $ do
      (ty, ctx, n) <- fresh3
      concl $ notInCtx2 (cons ty ctx) (suc n)
      -- GOOD: ty comes from conclusion input pattern, so it's grounded
      -- lookupCtx has modes [I, I, O], so AllVars = {0,1,2} ∪ {2} = {0,1,2}
      -- After concl, {0,1,2} are all grounded (from input positions)
      neg $ lookupCtx (cons ty ctx) (suc n) ty
      prem $ notInCtx2 ctx n
  ]

--------------------------------------------------------------------------------
-- BAD: badCheck - ungrounded variable in negation
-- UNCOMMENT THIS TO SEE THE COMPILE-TIME ERROR!
--------------------------------------------------------------------------------

{-
badCheck :: (RedexNeg rel, LogicType Ctx, LogicType Nat, LogicType Ty)
         => T vs1 Ctx rel -> T vs2 Nat rel
         -> AppliedM rel "badCheck" '[I, I] '[vs1, vs2] '[Ctx, Nat]
badCheck = defJudge2 @"badCheck" $ \rule ->
  [ rule "bad" $ do
      (ctx, n, ty) <- fresh3  -- ty is var 2, NEVER grounded!
      concl $ badCheck ctx n
      -- BAD: ty (var 2) is not grounded - it's not in concl inputs
      -- and no prem produces it before the negation
      neg $ lookupCtx ctx n ty  -- ERROR!
  ]
-}
