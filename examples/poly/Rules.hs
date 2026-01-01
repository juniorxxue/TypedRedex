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
import TypedRedex.Nominal.Prelude (Nom, TyNom)
import TypedRedex.Nominal (RedexFresh(..), bindT, substoM)
import TypedRedex.DSL.Moded
  ( MJudgment2, MJudgment3, MJudgment4, MJudgment5, In, Out
  , defJudge2, defJudge3, defJudge4, defJudge5
  , fresh, fresh2, fresh3, fresh4, fresh5, fresh6, prem, concl
  , unbind2M
  , return, (>>=), (>>)
  , (=/=)
  )

import Syntax

--------------------------------------------------------------------------------
-- Type constraint
--------------------------------------------------------------------------------

type PolyRel rel = (RedexFresh rel, RedexEval rel, RedexNeg rel, RedexHash rel)

--------------------------------------------------------------------------------
-- ssub: Polarized subtyping (single judgment with Polar argument)
--------------------------------------------------------------------------------


flipPolar :: PolyRel rel => MJudgment2 rel "flipPolar" (In Polar) (Out Polar)
flipPolar = defJudge2 @"flipPolar" flipPolarFmt $ \rule ->
  [ rule "pos" $ concl $ flipPolar pos neg
  , rule "neg" $ concl $ flipPolar neg pos
  ]
  where
    flipPolarFmt [p, p'] = formatPolarBar p ++ " = " ++ formatPolarVal p'
      where
        formatPolarBar x
          | x == "≤⁺" = "⁺̄"
          | x == "≤⁻" = "⁻̄"
          | otherwise = x ++ "̄"
        formatPolarVal x
          | x == "≤⁺" = "⁺"
          | x == "≤⁻" = "⁻"
          | otherwise = x
    flipPolarFmt args = "flipPolar(" ++ unwords args ++ ")"


lookupTmVar :: PolyRel rel => MJudgment3 rel "lookupVar" (In Env) (In Nom) (Out Ty)
lookupTmVar = undefined

lookupUvar :: PolyRel rel => MJudgment2 rel "lookupUvar" (In Env) (In TyNom)
lookupUvar = undefined

lookupBoundVar :: PolyRel rel => MJudgment4 rel "lookBoundVar" (In Env) (In TyNom) (Out Ty) (Out Ty)
lookupBoundVar = undefined

updateUpper :: PolyRel rel => MJudgment4 rel "updateUpper" (In Env) (In TyNom) (In Ty) (Out Env)
updateUpper = undefined

updateLower :: PolyRel rel => MJudgment4 rel "updateUpper" (In Env) (In TyNom) (In Ty) (Out Env)
updateLower = undefined

splitEnv :: PolyRel rel => MJudgment5 rel "splitEnv" (In Env) (In TyNom) (Out Env) (Out TyNom) (Out TyNom)
splitEnv = undefined

unsplitEnv :: PolyRel rel => MJudgment5 rel "unsplitEnv" (In Env) (In TyNom) (In TyNom) (In TyNom) (Out Env)
unsplitEnv = undefined

test_eq :: PolyRel rel => MJudgment2 rel "test_eq" (In Ty) (In Ty)
test_eq = defJudge2 @"test_eq" format $ \rule ->
  [ rule "refl" $ do
      ty <- fresh
      concl $ test_eq ty ty,

    rule "forall" $ do
      (bd1, bd2) <- fresh2
      (a, ty1, ty2) <- unbind2M bd1 bd2
      prem  $ test_eq ty1 ty2
      concl $ test_eq (tforall bd1) (tforall bd2)
  ]
  where format args = "test(" ++ unwords args ++ ")"

inst :: PolyRel rel => MJudgment5 rel "test_eq" (In Ty) (In TyNom) (In Ty) (In Ty) (Out Ty)
inst = undefined

ssub :: PolyRel rel => MJudgment5 rel "sub" (In Env) (In Ty) (In Polar) (In Ty) (Out Env)
ssub = defJudge5 @"sub" format $ \rule ->
  [ rule "int" $ do
      (p, env) <- fresh2
      concl $ ssub env tint p tint env

  , rule "uvar" $ do
      (env, a, p) <- fresh3
      prem  $ lookupUvar env a
      concl $ ssub env (tvar a) p (tvar a) env

  , rule "top" $ do
      (env, tyA, p) <- fresh3
      concl $ ssub env tyA p ttop env

  , rule "bot" $ do
      (tyA, p, env) <- fresh3
      concl $ ssub env tbot p tyA env

  , rule "var-l" $ do
      (tyA, tyB, tyC, env1, env2, a) <- fresh6
      prem  $ lookupBoundVar env1 a tyB tyC
      prem  $ updateUpper env1 a tyA env2
      concl $ ssub env1 (tvar a) pos tyA env2

  , rule "var-r" $ do
      (tyA, tyB, tyC, env1, env2, a) <- fresh6
      prem  $ lookupBoundVar env1 a tyB tyC
      prem  $ updateLower env1 a tyA env2
      concl $ ssub env1 tyA neg (tvar a) env2

  , rule "arr" $ do
      (p, p', env1, env2, env3) <- fresh5
      (tyA, tyB, tyC, tyD) <- fresh4
      prem  $ flipPolar p p'
      prem  $ ssub env1 tyC p' tyA env2
      prem  $ ssub env2 tyB p tyD env3
      concl $ ssub env1 (tarr tyA tyB) p (tarr tyC tyD) env3

  , rule "forall" $ do
      (env1, env2, p) <- fresh3
      (bd1, bd2) <- fresh2
      (a, tyA, tyB) <- unbind2M bd1 bd2
      prem  $ ssub (euvar a env1) tyA p tyB (euvar a env2)
      concl $ ssub env1 (tforall bd1) p (tforall bd2) env2
  ]
  where format [env1, ty1, polar, ty2, env2] = env1 ++ " |- " ++ ty1 ++ polar ++ ty2 ++ " ⊣ " ++ env2
        format args = "ssub(" ++ unwords args ++ ")"

sub :: PolyRel rel => MJudgment5 rel "sub" (In Env) (In Ty) (In Context) (Out Env) (Out Ty)
sub = defJudge5 @"sub" format $ \rule ->
  [ rule "empty" $ do
      (env, ty) <- fresh2
      concl $ sub env ty cempty env ty

  , rule "type" $ do
      (env1, env2, tyA, tyB) <- fresh4
      prem  $ ssub env1 tyA neg tyB env2
      concl $ sub env1 tyA (ctype tyB) env2 tyB

  , rule "forallL" $ do
      (tyA, tyB, tyC, tyD) <- fresh4
      (a, env1, env2) <- fresh3
      (tm, ctx, inst_ty) <- fresh3
      prem  $ inst tyC a tyD tyB inst_ty
      prem  $ sub (ebound tbot a ttop env1) tyA (ctm tm ctx) (ebound tyC a tyD env2) tyB
      concl $ sub env1 (tforall (bindT a tyA)) (ctm tm ctx) env2 inst_ty

  , rule "term" $ do
      (env1, env2, env3) <- fresh3
      (tyA, tyB, tyD, tyA') <- fresh4
      (ctx, tm) <- fresh2
      prem  $ infer env1 (ctype tyA) tm tyA' env2
      prem  $ sub env2  tyB ctx env3 tyD
      concl $ sub env1 (tarr tyA tyB) (ctm tm ctx) env3 (tarr tyA' tyD)

  , rule "svar" $ do
      (tyA, tyB, tyC) <- fresh3
      (env1, env2) <- fresh2
      (a, ctx) <- fresh2
      prem  $ lookupBoundVar env1 a tyA tyB
      prem  $ sub env1 tyB ctx env2 tyC
      concl $ sub env1 (tvar a) ctx env2 tyC
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

  , rule "sub" $ do
      (env1, _env, env2) <- fresh3
      (ctx, g, tyA, tyB) <- fresh4
      prem  $ infer env1 cempty g tyA _env
      ctx =/= cempty
      prem  $ sub env1 tyA ctx env2 tyB
      concl $ infer env1 ctx g tyB env2
  ]
  where
    format [env1, ctx, tm, ty, env2] = env1 ++ " |- " ++ ctx ++ " => " ++ tm ++ " => " ++ ty ++ " ⊣ " ++ env2
    format args = "infer(" ++ unwords args ++ ")"
