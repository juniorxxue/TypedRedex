{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RebindableSyntax #-}

-- | Polarized subtyping rules matching Poly/app/Infer.hs exactly
-- ssub :: (Env, Env) -> Ty -> Polar -> Ty -> m Env
module Rules where

import Prelude hiding ((>>=), (>>), return)
import TypedRedex hiding (fresh, fresh2, fresh3, fresh4, fresh5, fresh6, ground, lift1, lift2, lift3, neg)
import TypedRedex.Logic (RedexHash)
import TypedRedex.Nominal.Prelude
import TypedRedex.Nominal (RedexFresh(..), bindT, Substo(..), substoM)
import TypedRedex.DSL.Moded
  ( Mode(..), T(..)
  , AppliedM(..), MJudgment3, MJudgment4, MJudgment5, In, Out
  , defJudge3, defJudge4, defJudge5
  , fresh, fresh2, fresh3, fresh4, fresh5, fresh6, prem, concl
  , ground, Union
  , return, (>>=), (>>)
  , (===), (=/=)
  )

import Syntax
import Data.Data (typeOf3)

--------------------------------------------------------------------------------
-- Type constraint
--------------------------------------------------------------------------------

type PolyRel rel = (RedexFresh rel, RedexEval rel, RedexNeg rel, RedexHash rel)

--------------------------------------------------------------------------------
-- Judgment format functions
--------------------------------------------------------------------------------

-- unused, but left for futher reference

-- -- | Format: α̂ ∈ Δ
-- isEvarFmt :: [String] -> String
-- isEvarFmt [env, a] = a ++ "̂ ∈ " ++ env
-- isEvarFmt args = "isEvar(" ++ unwords args ++ ")"

-- -- | Format: α = τ ∈ Δ
-- isSvarFmt :: [String] -> String
-- isSvarFmt [env, a, ty] = a ++ " = " ++ ty ++ " ∈ " ++ env
-- isSvarFmt args = "isSvar(" ++ unwords args ++ ")"

-- -- | Format: Δ[α̂ := τ] = Δ'
-- instFmt :: [String] -> String
-- instFmt [env, a, ty, env'] = env ++ "[" ++ a ++ "̂ := " ++ ty ++ "] = " ++ env'
-- instFmt args = "inst(" ++ unwords args ++ ")"

-- -- | Format: p̄ = p'
-- flipPolarFmt :: [String] -> String
-- flipPolarFmt [p, p'] = formatPolarBar p ++ " = " ++ formatPolarVal p'
--   where
--     formatPolarBar x
--       | x == "≤⁺" = "⁺̄"
--       | x == "≤⁻" = "⁻̄"
--       | otherwise = x ++ "̄"
--     formatPolarVal x
--       | x == "≤⁺" = "⁺"
--       | x == "≤⁻" = "⁻"
--       | otherwise = x
-- flipPolarFmt args = "flipPolar(" ++ unwords args ++ ")"

--------------------------------------------------------------------------------
-- ssub: Polarized subtyping (single judgment with Polar argument)
--------------------------------------------------------------------------------


-- flipPolar :: PolyRel rel => MJudgment2 rel "flipPolar" (In Polar) (Out Polar)
-- flipPolar = defJudge2 @"flipPolar" flipPolarFmt $ \rule ->
--   [ rule "pos" $ concl $ flipPolar pos neg
--   , rule "neg" $ concl $ flipPolar neg pos
--   ]


lookupTmVar :: PolyRel rel => MJudgment3 rel "lookupVar" (In Env) (In Nom) (Out Ty)
lookupTmVar = undefined

lookupBoundVar :: PolyRel rel => MJudgment4 rel "lookBoundVar" (In Env) (In TyNom) (Out Ty) (Out Ty)
lookupBoundVar = undefined

splitEnv :: PolyRel rel => MJudgment5 rel "splitEnv" (In Env) (In TyNom) (Out Env) (Out TyNom) (Out TyNom)
splitEnv = undefined

unsplitEnv :: PolyRel rel => MJudgment5 rel "unsplitEnv" (In Env) (In TyNom) (In TyNom) (In TyNom) (Out Env)
unsplitEnv = undefined

sub :: PolyRel rel => MJudgment5 rel "sub" (In Env) (In Ty) (In Context) (Out Env) (Out Ty)
sub = defJudge5 @"sub" format $ \rule ->
  [ rule "empty" $ do
      (env, ty) <- fresh2
      concl $ sub env ty cempty env ty
  ]
  where format [env1, ty1, ctx, env2, ty2] = env1 ++ " |- " ++ ty1 ++ " <: " ++ ctx ++ " ⊣ " ++ env2 ++ " ~> " ++ ty2
        format args = "sub(" ++ unwords args ++ ")"


infer :: PolyRel rel => MJudgment5 rel "infer" (In Env) (In Context) (In Tm) (Out Ty) (Out Env)
infer = defJudge5 @"infer" format $ \rule ->
  [ rule "lit" $ do
      (n, env) <- fresh2
      concl $ infer env cempty (lit n) tint env

  , rule "var" $ do
      (x, ty, env) <- fresh3
      prem $ lookupTmVar env x ty
      concl $ infer env cempty (var x) ty env

  , rule "ann" $ do
      (tm, ty, env1, env2) <- fresh4
      prem $ infer env1 (ctype ty) tm ty env2
      concl $ infer env1 cempty (ann tm ty) ty env2

  , rule "lam1" $ do
      (x, tm, env1, env2) <- fresh4
      (ty1, ty2, ty3) <- fresh3
      prem  $ infer (etrm x ty1 env1) (ctype ty2) tm ty3 env2
      concl $ infer env1 (ctype (tarr ty1 ty2)) (lam (bindT x tm)) (tarr ty1 ty3) env2

  , rule "lam2" $ do
      (x, tm1, tm2, env1, ctx, env2) <- fresh6
      (ty1, ty2) <- fresh2
      prem  $ infer env1 cempty tm2 ty1 env2
      prem  $ infer (etrm x ty1 env1) ctx tm1 ty2 (etrm x ty1 env2)
      concl $ infer env1 (ctm tm2 ctx) (lam (bindT x tm1)) (tarr ty1 ty2) env2

  , rule "lam3" $ do
      (x, tm, env1, env2, env3, env4) <- fresh6
      (ty1, ty2, ty3) <- fresh3
      (a, b, c) <- fresh3
      prem  $ lookupBoundVar env1 a ty1 ty2
      prem  $ splitEnv env1 a env2 b c
      prem  $ infer (etrm x (tvar b) env2) (ctype (tvar c)) tm ty3 (etrm x (tvar b) env3)
      prem  $ unsplitEnv env3 a b c env4
      concl $ infer env1 (ctype (tvar a)) (lam (bindT x tm)) (tarr ty1 ty3) env4

  , rule "tlam1" $ do
      (a, tm, env1, env2, ty) <- fresh5
      prem  $ infer (euvar a env1) cempty tm ty (euvar a env2)
      concl $ infer env1 cempty (tlam (bindT a tm)) (tforall (bindT a ty)) env2
  
  , rule "tlam2" $ do
      (a, tm, env1, ty1, ty2, env2) <- fresh6
      prem  $ infer (euvar a env1) (ctype ty2) tm ty1 (euvar a env2)
      concl $ infer env1 (ctype (tforall (bindT a ty2))) (tlam (bindT a tm)) (tforall (bindT a ty1)) env2

  , rule "app" $ do
      (tm1, tm2, env1, ctx, env2) <- fresh5
      (ty1, ty2) <- fresh2
      prem  $ infer env1 (ctm tm2 ctx) tm1 (tarr ty1 ty2) env2
      concl $ infer env1 ctx (app tm1 tm2) ty2 env2
  
  , rule "tapp" $ do
      (tm, ty2, env1, ctx, env2, _env) <- fresh6
      (a, ty1, ty3, st_ty) <- fresh4
      prem  $ infer env1 cempty tm (tforall (bindT a ty1)) _env
      prem  $ substoM a ty1 ty2 st_ty
      prem  $ sub env1 st_ty ctx env2 ty3
      concl $ infer env1 ctx (tapp tm ty2) ty3 env2
      
  ]
  where
    format [env1, ctx, tm, ty, env2] = env1 ++ " |- " ++ ctx ++ " => " ++ tm ++ " => " ++ ty ++ " ⊣ " ++ env2
    format args = "infer(" ++ unwords args ++ ")"
