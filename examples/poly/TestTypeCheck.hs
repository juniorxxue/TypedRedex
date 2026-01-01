{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RebindableSyntax #-}

-- | Test file to measure type-checking speed without scope errors
--
-- === Profiling Instructions ===
--
-- 1. Clean build with timing:
--    cabal clean && time cabal build example-poly
--
-- 2. Incremental rebuild (touch this file):
--    touch TestTypeCheck.hs && time cabal build example-poly
--
-- 3. With GHC timing stats:
--    cabal build example-poly --ghc-options="-ddump-timings"
--
-- 4. Limit type family reduction depth (will error if exceeded):
--    cabal build example-poly --ghc-options="-freduction-depth=50"
--
-- 5. Test individual rules by commenting out others
--
-- === Expected Results ===
--
-- On M1 Mac with GHC 9.10.1:
-- - inferTest1 (1 complex rule, 12 vars, 4 prems): ~30-60 sec
-- - inferTest2 (1 rule, 14 vars, 5 prems): ~60-90 sec
-- - inferTest4 (5 rules): ~3-4 min
--
-- If your times are similar, the issue is type-family computation cost.
-- If much faster, something else is causing your HLS issues.
--
module TestTypeCheck where

import Prelude hiding ((>>=), (>>), return)
import TypedRedex hiding (fresh, ground, lift1, lift2, lift3, neg)
import TypedRedex.Logic (RedexHash)
import TypedRedex.Nominal.Prelude
import TypedRedex.Nominal (RedexFresh(..), bindT)
import TypedRedex.DSL.Moded
  ( Mode(..), T(..)
  , AppliedM(..), MJudgment2, MJudgment3, MJudgment4, MJudgment5, MJudgment6, In, Out
  , defJudge2, defJudge3, defJudge4, defJudge5, defJudge6, ModedRule(..)
  , fresh, prem, concl
  , ground, Union
  , return, (>>=), (>>)
  , (===), (=/=)
  )

import Syntax

type PolyRel rel = (RedexFresh rel, RedexEval rel, RedexNeg rel, RedexHash rel)

--------------------------------------------------------------------------------
-- Helper judgments (undefined - just for type-checking)
--------------------------------------------------------------------------------

lookupBoundVar' :: PolyRel rel => MJudgment4 rel "lookBoundVar" (In Env) (In TyNom) (Out Ty) (Out Ty)
lookupBoundVar' = undefined

splitEnv' :: PolyRel rel => MJudgment5 rel "splitEnv" (In Env) (In TyNom) (Out Env) (Out TyNom) (Out TyNom)
splitEnv' = undefined

unsplitEnv' :: PolyRel rel => MJudgment5 rel "unsplitEnv" (In Env) (In TyNom) (In TyNom) (In TyNom) (Out Env)
unsplitEnv' = undefined

--------------------------------------------------------------------------------
-- Test 1: Single complex rule (12 fresh vars, 4 premises)
-- Comment out Tests 2-4 to isolate this test
--------------------------------------------------------------------------------

inferTest1 :: PolyRel rel => MJudgment5 rel "inferTest1" (In Env) (In Context) (In Tm) (Out Ty) (Out Env)
inferTest1 = defJudge5 @"inferTest1" format $ \rule ->
  [ rule "lam3-fixed" $ do
      (x, tm, env1, env2, env3) <- fresh
      (ty1, ty2, ty3) <- fresh
      (a, b, c) <- fresh
      env4 <- fresh
      prem  $ lookupBoundVar' env1 a ty1 ty2
      prem  $ splitEnv' env1 a env2 b c
      prem  $ inferTest1 (etrm x (tvar b) env2) (ctype (tvar c)) tm ty3 (etrm x (tvar b) env3)
      prem  $ unsplitEnv' env3 a b c env4
      concl $ inferTest1 env1 (ctype (tvar a)) (lam (bindT x tm)) (tarr ty1 ty3) env4
  ]
  where
    format [env1, ctx, tm, ty, env2] = env1 ++ " |- " ++ ctx ++ " => " ++ tm ++ " => " ++ ty ++ " ⊣ " ++ env2
    format args = "inferTest1(" ++ unwords args ++ ")"

--------------------------------------------------------------------------------
-- Test 2: Even more complex rule (14 fresh vars, 5 premises)
-- Comment out to speed up compilation
--------------------------------------------------------------------------------

inferTest2 :: PolyRel rel => MJudgment5 rel "inferTest2" (In Env) (In Context) (In Tm) (Out Ty) (Out Env)
inferTest2 = defJudge5 @"inferTest2" format $ \rule ->
  [ rule "complex" $ do
      (x, tm, env1, env2, _env3) <- fresh
      (ty1, ty2, ty3) <- fresh
      (a, b, c) <- fresh
      (env4, env5, env6) <- fresh
      prem  $ lookupBoundVar' env1 a ty1 ty2
      prem  $ splitEnv' env1 a env2 b c
      prem  $ inferTest2 (etrm x (tvar b) env2) (ctype (tvar c)) tm ty3 env4
      prem  $ unsplitEnv' env4 a b c env5
      prem  $ unsplitEnv' env5 a b c env6
      concl $ inferTest2 env1 (ctype (tvar a)) (lam (bindT x tm)) (tarr ty1 ty3) env6
  ]
  where
    format [env1, ctx, tm, ty, env2] = env1 ++ " |- " ++ ctx ++ " => " ++ tm ++ " => " ++ ty ++ " ⊣ " ++ env2
    format args = "inferTest2(" ++ unwords args ++ ")"

--------------------------------------------------------------------------------
-- Test 3: Type error test (uncomment to test error detection speed)
-- This has a scheduling error: env4 used before grounded
--------------------------------------------------------------------------------

{-
inferTest3 :: PolyRel rel => MJudgment5 rel "inferTest3" (In Env) (In Context) (In Tm) (Out Ty) (Out Env)
inferTest3 = defJudge5 @"inferTest3" format $ \rule ->
  [ rule "bad-schedule" $ do
      (x, tm, env1, env2, env3) <- fresh
      (ty1, ty2, ty3) <- fresh
      (a, b, c) <- fresh
      env4 <- fresh
      -- BUG: env4 used as input before produced!
      prem  $ unsplitEnv' env4 a b c env3
      prem  $ lookupBoundVar' env1 a ty1 ty2
      prem  $ splitEnv' env1 a env2 b c
      prem  $ inferTest3 (etrm x (tvar b) env2) (ctype (tvar c)) tm ty3 (etrm x (tvar b) env3)
      concl $ inferTest3 env1 (ctype (tvar a)) (lam (bindT x tm)) (tarr ty1 ty3) env4
  ]
  where
    format args = "inferTest3(" ++ unwords args ++ ")"
-}

--------------------------------------------------------------------------------
-- Test 4: Multiple rules (stress test - 5 rules)
-- This simulates a realistic judgment with several rules
--------------------------------------------------------------------------------

inferTest4 :: PolyRel rel => MJudgment5 rel "inferTest4" (In Env) (In Context) (In Tm) (Out Ty) (Out Env)
inferTest4 = defJudge5 @"inferTest4" format $ \rule ->
  [ rule "rule1" $ do
      (n, env) <- fresh
      concl $ inferTest4 env cempty (lit n) tint env

  , rule "rule2" $ do
      (tm, ty, env1, env2) <- fresh
      prem $ inferTest4 env1 (ctype ty) tm ty env2
      concl $ inferTest4 env1 cempty (ann tm ty) ty env2

  , rule "rule3" $ do
      (x, tm, env1, env2) <- fresh
      (ty1, ty2, ty3) <- fresh
      prem  $ inferTest4 (etrm x ty1 env1) (ctype ty2) tm ty3 env2
      concl $ inferTest4 env1 (ctype (tarr ty1 ty2)) (lam (bindT x tm)) (tarr ty1 ty3) env2

  , rule "rule4" $ do
      (x, tm1, tm2, env1, ctx, env2) <- fresh
      (ty1, ty2) <- fresh
      prem  $ inferTest4 env1 cempty tm2 ty1 env2
      prem  $ inferTest4 (etrm x ty1 env1) ctx tm1 ty2 (etrm x ty1 env2)
      concl $ inferTest4 env1 (ctm tm2 ctx) (lam (bindT x tm1)) (tarr ty1 ty2) env2

  , rule "rule5" $ do
      (x, tm, env1, env2, env3) <- fresh
      (ty1, ty2, ty3) <- fresh
      (a, b, c) <- fresh
      env4 <- fresh
      prem  $ lookupBoundVar' env1 a ty1 ty2
      prem  $ splitEnv' env1 a env2 b c
      prem  $ inferTest4 (etrm x (tvar b) env2) (ctype (tvar c)) tm ty3 (etrm x (tvar b) env3)
      prem  $ unsplitEnv' env3 a b c env4
      concl $ inferTest4 env1 (ctype (tvar a)) (lam (bindT x tm)) (tarr ty1 ty3) env4
  ]
  where
    format [env1, ctx, tm, ty, env2] = env1 ++ " |- " ++ ctx ++ " => " ++ tm ++ " => " ++ ty ++ " ⊣ " ++ env2
    format args = "inferTest4(" ++ unwords args ++ ")"
