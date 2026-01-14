{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RebindableSyntax #-}

-- | Polarized subtyping rules matching Poly/app/Infer.hs exactly
-- ssub :: (Env, Env) -> Ty -> Polar -> Ty -> m Env
module Rules where

import Prelude hiding ((>>=), (>>), return)
import TypedRedex hiding (fresh, ground, lift1, lift2, lift3, neg)
import TypedRedex.Logic (HasDisplay, RedexHash)
import TypedRedex.Nominal.Prelude (Nom, TyNom)
import TypedRedex.Nominal (Bind, Permute, RedexFresh(..), bindT, substoM)
import TypedRedex.DSL.Moded
  ( MJudgment2, MJudgment3, MJudgment4, MJudgment5, MJudgment6, In, Out
  , RuleM
  , T(..)
  , Union
  , defJudge2, defJudge3, defJudge4, defJudge5, defJudge6
  , fresh, prem, concl
  , return, (>>=), (>>)
  , (=/=)
  , unbind2M
  , freshTyNomM
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
flipPolar = defJudge2 flipPolarFmt $ \rule ->
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
lookupTmVar = defJudge3 format $ \rule ->
  [ rule "here" $ do
      (x, ty, env) <- fresh
      concl $ lookupTmVar (etrm x ty env) x ty

  , rule "skip-trm" $ do
      (x, y, ty, ty', env) <- fresh
      x =/= y
      prem  $ lookupTmVar env x ty
      concl $ lookupTmVar (etrm y ty' env) x ty

  , rule "skip-uvar" $ do
      (x, a, ty, env) <- fresh
      prem  $ lookupTmVar env x ty
      concl $ lookupTmVar (euvar a env) x ty

  , rule "skip-bound" $ do
      (x, a, tyL, tyU, ty, env) <- fresh
      prem  $ lookupTmVar env x ty
      concl $ lookupTmVar (ebound tyL a tyU env) x ty
  ]
  where
    format [env, x, ty] = env ++ " ∋ " ++ x ++ " : " ++ ty
    format args = "lookupTmVar(" ++ unwords args ++ ")"

lookupUvar :: PolyRel rel => MJudgment2 rel "lookupUvar" (In Env) (In TyNom)
lookupUvar = defJudge2 format $ \rule ->
  [ rule "here" $ do
      (a, env) <- fresh
      concl $ lookupUvar (euvar a env) a

  , rule "skip-trm" $ do
      (a, x, ty, env) <- fresh
      prem  $ lookupUvar env a
      concl $ lookupUvar (etrm x ty env) a

  , rule "skip-uvar" $ do
      (a, b, env) <- fresh
      a =/= b
      prem  $ lookupUvar env a
      concl $ lookupUvar (euvar b env) a

  , rule "skip-bound" $ do
      (a, b, tyL, tyU, env) <- fresh
      prem  $ lookupUvar env a
      concl $ lookupUvar (ebound tyL b tyU env) a
  ]
  where
    format [env, a] = env ++ " ∋ " ++ a
    format args = "lookupUvar(" ++ unwords args ++ ")"

lookupBoundVar :: PolyRel rel => MJudgment4 rel "lookBoundVar" (In Env) (In TyNom) (Out Ty) (Out Ty)
lookupBoundVar = defJudge4 format $ \rule ->
  [ rule "here" $ do
      (a, tyL, tyU, env) <- fresh
      concl $ lookupBoundVar (ebound tyL a tyU env) a tyL tyU

  , rule "skip-trm" $ do
      (a, x, ty, tyL, tyU, env) <- fresh
      prem  $ lookupBoundVar env a tyL tyU
      concl $ lookupBoundVar (etrm x ty env) a tyL tyU

  , rule "skip-uvar" $ do
      (a, b, tyL, tyU, env) <- fresh
      prem  $ lookupBoundVar env a tyL tyU
      concl $ lookupBoundVar (euvar b env) a tyL tyU

  , rule "skip-bound" $ do
      (a, b, tyL, tyU) <- fresh
      (tyL', tyU', env) <- fresh
      a =/= b
      prem  $ lookupBoundVar env a tyL tyU
      concl $ lookupBoundVar (ebound tyL' b tyU' env) a tyL tyU
  ]
  where
    format [env, a, tyL, tyU] = env ++ " ∋ " ++ tyL ++ " <: " ++ a ++ " <: " ++ tyU
    format args = "lookupBoundVar(" ++ unwords args ++ ")"

-- | Greatest lower bound (meet) of two types - used for upper bound updates
glb :: PolyRel rel => MJudgment3 rel "glb" (In Ty) (In Ty) (Out Ty)
glb = defJudge3 format $ \rule ->
  [ rule "bot-l" $ do
      ty <- fresh
      concl $ glb tbot ty tbot

  , rule "bot-r" $ do
      ty <- fresh
      concl $ glb ty tbot tbot

  , rule "top-l" $ do
      ty <- fresh
      concl $ glb ttop ty ty

  , rule "top-r" $ do
      ty <- fresh
      concl $ glb ty ttop ty

  , rule "int" $ concl $ glb tint tint tint

  , rule "var" $ do
      a <- fresh
      concl $ glb (tvar a) (tvar a) (tvar a)

  , rule "arr" $ do
      (tyA, tyB, tyC, tyD, tyAC, tyBD) <- fresh
      prem  $ lub tyA tyC tyAC  -- contravariant in domain
      prem  $ glb tyB tyD tyBD  -- covariant in codomain
      concl $ glb (tarr tyA tyB) (tarr tyC tyD) (tarr tyAC tyBD)
  ]
  where
    format [ty1, ty2, ty3] = ty1 ++ " ∧ " ++ ty2 ++ " = " ++ ty3
    format args = "glb(" ++ unwords args ++ ")"

-- | Least upper bound (join) of two types - used for lower bound updates
lub :: PolyRel rel => MJudgment3 rel "lub" (In Ty) (In Ty) (Out Ty)
lub = defJudge3 format $ \rule ->
  [ rule "top-l" $ do
      ty <- fresh
      concl $ lub ttop ty ttop

  , rule "top-r" $ do
      ty <- fresh
      concl $ lub ty ttop ttop

  , rule "bot-l" $ do
      ty <- fresh
      concl $ lub tbot ty ty

  , rule "bot-r" $ do
      ty <- fresh
      concl $ lub ty tbot ty

  , rule "int" $ concl $ lub tint tint tint

  , rule "var" $ do
      a <- fresh
      concl $ lub (tvar a) (tvar a) (tvar a)

  , rule "arr" $ do
      (tyA, tyB, tyC, tyD, tyAC, tyBD) <- fresh
      prem  $ glb tyA tyC tyAC  -- contravariant in domain
      prem  $ lub tyB tyD tyBD  -- covariant in codomain
      concl $ lub (tarr tyA tyB) (tarr tyC tyD) (tarr tyAC tyBD)
  ]
  where
    format [ty1, ty2, ty3] = ty1 ++ " ∨ " ++ ty2 ++ " = " ++ ty3
    format args = "lub(" ++ unwords args ++ ")"

-- | Update upper bound: find a's bounds and compute meet with new bound
updateUpper :: PolyRel rel => MJudgment4 rel "updateUpper" (In Env) (In TyNom) (In Ty) (Out Env)
updateUpper = defJudge4 format $ \rule ->
  [ rule "here" $ do
      (a, tyL, tyU, tyU', tyNew, env) <- fresh
      prem  $ glb tyU tyNew tyU'
      concl $ updateUpper (ebound tyL a tyU env) a tyNew (ebound tyL a tyU' env)

  , rule "skip-trm" $ do
      (a, x, ty, tyNew, env, env') <- fresh
      prem  $ updateUpper env a tyNew env'
      concl $ updateUpper (etrm x ty env) a tyNew (etrm x ty env')

  , rule "skip-uvar" $ do
      (a, b, tyNew, env, env') <- fresh
      prem  $ updateUpper env a tyNew env'
      concl $ updateUpper (euvar b env) a tyNew (euvar b env')

  , rule "skip-bound" $ do
      (a, b, tyNew, env, env') <- fresh
      (tyL', tyU') <- fresh
      a =/= b
      prem  $ updateUpper env a tyNew env'
      concl $ updateUpper (ebound tyL' b tyU' env) a tyNew (ebound tyL' b tyU' env')
  ]
  where
    format [env, a, ty, env'] = env ++ "[" ++ a ++ " upper ∧= " ++ ty ++ "] = " ++ env'
    format args = "updateUpper(" ++ unwords args ++ ")"

-- | Update lower bound: find a's bounds and compute join with new bound
updateLower :: PolyRel rel => MJudgment4 rel "updateLower" (In Env) (In TyNom) (In Ty) (Out Env)
updateLower = defJudge4 format $ \rule ->
  [ rule "here" $ do
      (a, tyL, tyL', tyU, tyNew, env) <- fresh
      prem  $ lub tyL tyNew tyL'
      concl $ updateLower (ebound tyL a tyU env) a tyNew (ebound tyL' a tyU env)

  , rule "skip-trm" $ do
      (a, x, ty, tyNew, env, env') <- fresh
      prem  $ updateLower env a tyNew env'
      concl $ updateLower (etrm x ty env) a tyNew (etrm x ty env')

  , rule "skip-uvar" $ do
      (a, b, tyNew, env, env') <- fresh
      prem  $ updateLower env a tyNew env'
      concl $ updateLower (euvar b env) a tyNew (euvar b env')

  , rule "skip-bound" $ do
      (a, b, tyNew, env, env') <- fresh
      (tyL', tyU') <- fresh
      a =/= b
      prem  $ updateLower env a tyNew env'
      concl $ updateLower (ebound tyL' b tyU' env) a tyNew (ebound tyL' b tyU' env')
  ]
  where
    format [env, a, ty, env'] = env ++ "[" ++ a ++ " lower ∨= " ++ ty ++ "] = " ++ env'
    format args = "updateLower(" ++ unwords args ++ ")"


splittable :: PolyRel rel => MJudgment6 rel "splittable" (In Ty) (In Ty) (Out Ty) (Out Ty) (Out Ty) (Out Ty)
splittable = defJudge6 format $ \rule ->
    [ rule "arr" $ do
        (tyA, tyB, tyC, tyD) <- fresh
        concl $ splittable (tarr tyA tyB) (tarr tyC tyD) tyC tyA tyB tyD

    -- , rule "top" $ do
    --     () <- fresh
    --     concl $ splittable tyA ttop tbot
    ]
    where
      format [tyL, tyU, tyC, tyA, tyB, tyD] =
        tyL ++ " <: " ++ tyU ++ " splittable into " ++ tyC ++ ", " ++ tyA ++ " -> " ++ tyB ++ ", " ++ tyD
      format args = "splittable(" ++ unwords args ++ ")"

-- splitEnv says we have a variable (alpha) in the environment, whose bounds are "splitable" (function forms)
-- then we produce a new environment by splitting alpha into beta and gamma, where beta and gamma's bounds are the components of alpha's bounds
-- alpha ~~~ beta -> gamma
-- example:
-- old env: int -> int <: a <: bot -> top
-- new env: bot <: b <: int, int <: c <: top
splitEnv :: PolyRel rel => MJudgment5 rel "splitEnv" (In Env) (In TyNom) (Out Env) (Out TyNom) (Out TyNom)
splitEnv = defJudge5 format $ \rule ->
  [ rule "split" $ do
      (a, env) <- fresh
      (tyL, tyU) <- fresh
      (tyUA, tyLA, tyLB, tyUB) <- fresh
      b <- freshTyNomM
      c <- freshTyNomM
      prem  $ lookupBoundVar env a tyL tyU
      prem  $ splittable tyL tyU tyUA tyLA tyLB tyUB
      -- a had: tyL <: a <: tyU where tyL = tyLA -> tyLB, tyU = tyUA -> tyUB
      -- b gets: tyUA <: b <: tyLA (domain, contravariant)
      -- c gets: tyLB <: c <: tyUB (codomain, covariant)
      concl $ splitEnv env a (ebound tyUA b tyLA (ebound tyLB c tyUB env)) b c
  ]
  where
    format [env, a, env', b, c] = env ++ "[" ++ a ++ " ~~> " ++ b ++ " -> " ++ c ++ "] = " ++ env'
    format args = "splitEnv(" ++ unwords args ++ ")"

-- a reverse of splitEnv
unsplitEnv :: PolyRel rel => MJudgment5 rel "unsplitEnv" (In Env) (In TyNom) (In TyNom) (Out TyNom) (Out Env)
unsplitEnv = defJudge5 format $ \rule ->
  [ rule "unsplit" $ do
      (b, c, env) <- fresh
      (tyUA, tyLA, tyLB, tyUB) <- fresh
      a <- freshTyNomM
      prem  $ lookupBoundVar env b tyUA tyLA
      prem  $ lookupBoundVar env c tyLB tyUB
      -- b had: tyUA <: b <: tyLA (domain, contravariant)
      -- c had: tyLB <: c <: tyUB (codomain, covariant)
      -- Reconstruct a: (tyLA -> tyLB) <: a <: (tyUA -> tyUB)
      concl $ unsplitEnv env b c a (ebound (tarr tyLA tyLB) a (tarr tyUA tyUB) env)
  ]
  where
    format [env, b, c, a, env'] = env ++ "[" ++ b ++ " -> " ++ c ++ " ~~> " ++ a ++ "] = " ++ env'
    format args = "unsplitEnv(" ++ unwords args ++ ")"

-- A <: a <: B
-- C (a may appear in C)
-- if a in co-variant position of C, replace with B, otherwise replace with A
inst :: PolyRel rel => MJudgment5 rel "inst" (In Ty) (In TyNom) (In Ty) (In Ty) (Out Ty)
inst = defJudge5 format $ \rule ->
  [ rule "inst" $ do
      (tyL, a, tyU, tyC, tyR) <- fresh
      prem  $ instP tyL a tyU pos tyC tyR
      concl $ inst tyL a tyU tyC tyR
  ]
  where
    format [tyL, a, tyU, tyC, tyR] = "[" ++ tyL ++ "<:" ++ a ++ "<:" ++ tyU ++ "]" ++ tyC ++ " = " ++ tyR
    format args = "inst(" ++ unwords args ++ ")"

-- | Instantiation with polarity tracking
-- instP tyLower a tyUpper polarity tyC result
-- In positive position: replace a with tyUpper
-- In negative position: replace a with tyLower
instP :: PolyRel rel => MJudgment6 rel "instP" (In Ty) (In TyNom) (In Ty) (In Polar) (In Ty) (Out Ty)
instP = defJudge6 format $ \rule ->
  [ rule "var-pos" $ do
      (tyL, a, tyU) <- fresh
      concl $ instP tyL a tyU pos (tvar a) tyU

  , rule "var-neg" $ do
      (tyL, a, tyU) <- fresh
      concl $ instP tyL a tyU neg (tvar a) tyL

  , rule "var-other" $ do
      (tyL, a, tyU, p, b) <- fresh
      a =/= b
      concl $ instP tyL a tyU p (tvar b) (tvar b)

  , rule "int" $ do
      (tyL, a, tyU, p) <- fresh
      concl $ instP tyL a tyU p tint tint

  , rule "top" $ do
      (tyL, a, tyU, p) <- fresh
      concl $ instP tyL a tyU p ttop ttop

  , rule "bot" $ do
      (tyL, a, tyU, p) <- fresh
      concl $ instP tyL a tyU p tbot tbot

  , rule "arr" $ do
      (tyL, a, tyU, p, p') <- fresh
      (tyA, tyB, tyA', tyB') <- fresh
      prem  $ flipPolar p p'
      prem  $ instP tyL a tyU p' tyA tyA'  -- contravariant in domain
      prem  $ instP tyL a tyU p tyB tyB'   -- covariant in codomain
      concl $ instP tyL a tyU p (tarr tyA tyB) (tarr tyA' tyB')

  , rule "forall" $ do
      (tyL, a, tyU, p) <- fresh
      (bd, tyBody') <- fresh
      (b, tyBody, _tyBody) <- unbind2M bd bd
      a =/= b
      prem  $ instP tyL a tyU p tyBody tyBody'
      concl $ instP tyL a tyU p (tforall bd) (tforall (bindT b tyBody'))
  ]
  where
    format [tyL, a, tyU, p, tyC, tyR] = "[" ++ tyL ++ "<:" ++ a ++ "<:" ++ tyU ++ "]" ++ p ++ " " ++ tyC ++ " = " ++ tyR
    format args = "instP(" ++ unwords args ++ ")"

ssub :: PolyRel rel => MJudgment5 rel "sub" (In Env) (In Ty) (In Polar) (In Ty) (Out Env)
ssub = defJudge5 format $ \rule ->
  [ rule "int" $ do
      (p, env) <- fresh
      concl $ ssub env tint p tint env

  , rule "uvar" $ do
      (env, a, p) <- fresh
      prem  $ lookupUvar env a
      concl $ ssub env (tvar a) p (tvar a) env

  , rule "top" $ do
      (env, tyA, p) <- fresh
      concl $ ssub env tyA p ttop env

  , rule "bot" $ do
      (tyA, p, env) <- fresh
      concl $ ssub env tbot p tyA env

  , rule "var-l" $ do
      (tyA, tyB, tyC, env1, env2, a) <- fresh
      prem  $ lookupBoundVar env1 a tyB tyC
      prem  $ updateUpper env1 a tyA env2
      concl $ ssub env1 (tvar a) pos tyA env2

  , rule "var-r" $ do
      (tyA, tyB, tyC, env1, env2, a) <- fresh
      prem  $ lookupBoundVar env1 a tyB tyC
      prem  $ updateLower env1 a tyA env2
      concl $ ssub env1 tyA neg (tvar a) env2

  , rule "arr" $ do
      (p, p', env1, env2, env3) <- fresh
      (tyA, tyB, tyC, tyD) <- fresh
      prem  $ flipPolar p p'
      prem  $ ssub env1 tyC p' tyA env2
      prem  $ ssub env2 tyB p tyD env3
      concl $ ssub env1 (tarr tyA tyB) p (tarr tyC tyD) env3

  , rule "forall" $ do
      (env1, env2, p) <- fresh
      (bd1, bd2) <- fresh
      -- With unbind2M, order doesn't matter - the scheduler handles it
      (a, tyA, tyB) <- unbind2M bd1 bd2
      prem  $ ssub (euvar a env1) tyA p tyB (euvar a env2)
      concl $ ssub env1 (tforall bd1) p (tforall bd2) env2
  ]
  where format [env1, ty1, polar, ty2, env2] = env1 ++ " |- " ++ ty1 ++ " " ++ polar ++ " " ++ ty2 ++ " ⊣ " ++ env2
        format args = "ssub(" ++ unwords args ++ ")"

sub :: PolyRel rel => MJudgment5 rel "sub" (In Env) (In Ty) (In Context) (Out Env) (Out Ty)
sub = defJudge5 format $ \rule ->
  [ rule "empty" $ do
      (env, ty) <- fresh
      concl $ sub env ty cempty env ty

  , rule "type" $ do
      (env1, env2, tyA, tyB) <- fresh
      prem  $ ssub env1 tyA neg tyB env2
      concl $ sub env1 tyA (ctype tyB) env2 tyB

  , rule "forallL" $ do
      (tyA, tyB, tyC, tyD) <- fresh
      (a, env1, env2) <- fresh
      (tm, ctx, inst_ty) <- fresh
      prem  $ inst tyC a tyD tyB inst_ty
      prem  $ sub (ebound tbot a ttop env1) tyA (ctm tm ctx) (ebound tyC a tyD env2) tyB
      concl $ sub env1 (tforall (bindT a tyA)) (ctm tm ctx) env2 inst_ty

  , rule "term" $ do
      (env1, env2, env3) <- fresh
      (tyA, tyB, tyD, tyA') <- fresh
      (ctx, tm) <- fresh
      prem  $ infer env1 (ctype tyA) tm tyA' env2
      prem  $ sub env2  tyB ctx env3 tyD
      concl $ sub env1 (tarr tyA tyB) (ctm tm ctx) env3 (tarr tyA' tyD)

  , rule "svar" $ do
      (tyA, tyB, tyC) <- fresh
      (env1, env2) <- fresh
      (a, ctx) <- fresh
      prem  $ lookupBoundVar env1 a tyA tyB
      prem  $ sub env1 tyB ctx env2 tyC
      concl $ sub env1 (tvar a) ctx env2 tyC
  ]
  where format [env1, ty1, ctx, env2, ty2] = env1 ++ " |- " ++ ty1 ++ " <: " ++ ctx ++ " ⊣ " ++ env2 ++ " ~> " ++ ty2
        format args = "sub(" ++ unwords args ++ ")"


infer :: PolyRel rel => MJudgment5 rel "infer" (In Env) (In Context) (In Tm) (Out Ty) (Out Env)
infer = defJudge5 format $ \rule ->
  [ rule "lit" $ do
      (n, env) <- fresh
      concl $ infer env cempty (lit n) tint env

  , rule "var" $ do
      (x, ty, env) <- fresh
      prem $ lookupTmVar env x ty
      concl $ infer env cempty (var x) ty env

  , rule "ann" $ do
      (tm, ty, env1, env2) <- fresh
      prem $ infer env1 (ctype ty) tm ty env2
      -----------------------------------------------
      concl $ infer env1 cempty (ann tm ty) ty env2

  , rule "lam1" $ do
      (x, tm, env1, env2) <- fresh
      (ty1, ty2, ty3) <- fresh
      prem  $ infer (etrm x ty1 env1) (ctype ty2) tm ty3 (etrm x ty1 env2)
      concl $ infer env1 (ctype (tarr ty1 ty2)) (lam (bindT x tm)) (tarr ty1 ty3) env2

  , rule "lam2" $ do
      (x, tm1, tm2, env1, ctx, env2) <- fresh
      (ty1, ty2) <- fresh
      prem  $ infer env1 cempty tm2 ty1 env2
      prem  $ infer (etrm x ty1 env1) ctx tm1 ty2 (etrm x ty1 env2)
      concl $ infer env1 (ctm tm2 ctx) (lam (bindT x tm1)) (tarr ty1 ty2) env2

  , rule "lam3" $ do
      (x, tm, env1, env2, env3, env4) <- fresh
      (ty1, ty2, ty3) <- fresh
      (a, b, c) <- fresh
      prem  $ lookupBoundVar env1 a ty1 ty2
      prem  $ splitEnv env1 a env2 b c
      prem  $ infer (etrm x (tvar b) env2) (ctype (tvar c)) tm ty3 (etrm x (tvar b) env3)
      prem  $ unsplitEnv env3 a b c env4
      concl $ infer env1 (ctype (tvar a)) (lam (bindT x tm)) (tarr ty1 ty3) env4

  , rule "tlam1" $ do
      (a, tm, env1, env2, ty) <- fresh
      prem  $ infer (euvar a env1) cempty tm ty (euvar a env2)
      concl $ infer env1 cempty (tlam (bindT a tm)) (tforall (bindT a ty)) env2

  , rule "tlam2" $ do
      (a, tm, env1, ty1, ty2, env2) <- fresh
      prem  $ infer (euvar a env1) (ctype ty2) tm ty1 (euvar a env2)
      concl $ infer env1 (ctype (tforall (bindT a ty2))) (tlam (bindT a tm)) (tforall (bindT a ty1)) env2

  , rule "app" $ do
      (tm1, tm2, env1, ctx, env2) <- fresh
      (ty1, ty2) <- fresh
      prem  $ infer env1 (ctm tm2 ctx) tm1 (tarr ty1 ty2) env2
      concl $ infer env1 ctx (app tm1 tm2) ty2 env2

  , rule "tapp" $ do
      (tm, ty2, env1, ctx, env2, _env) <- fresh
      (a, ty1, ty3, st_ty) <- fresh
      prem  $ infer env1 cempty tm (tforall (bindT a ty1)) _env
      prem  $ substoM a ty1 ty2 st_ty
      prem  $ sub env1 st_ty ctx env2 ty3
      concl $ infer env1 ctx (tapp tm ty2) ty3 env2

  , rule "sub" $ do
      (env1, _env, env2) <- fresh
      (ctx, g, tyA, tyB) <- fresh
      prem  $ infer env1 cempty g tyA _env
      ctx =/= cempty
      prem  $ sub env1 tyA ctx env2 tyB
      concl $ infer env1 ctx g tyB env2

  , rule "plus" $ do
        (tm1, tm2, env1, _env2, _env3) <- fresh
        prem  $ infer env1 cempty tm1 tint _env2
        prem  $ infer env1 cempty tm2 tint _env3
        concl $ infer env1 cempty (plus tm1 tm2) tint env1

  , rule "true" $ do
        env <- fresh
        concl $ infer env cempty true tbool env

  , rule "false" $ do
        env <- fresh
        concl $ infer env cempty false tbool env


  , rule "false" $ do
        env <- fresh
        concl $ infer env cempty false tint env
  ]
  where
    format [env1, ctx, tm, ty, env2] = env1 ++ " |- " ++ ctx ++ " => " ++ tm ++ " => " ++ ty ++ " ⊣ " ++ env2
    format args = "infer(" ++ unwords args ++ ")"
