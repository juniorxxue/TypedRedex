{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RebindableSyntax #-}

-- | Polarized subtyping rules matching Poly/app/Infer.hs exactly
-- ssub :: (Env, Env) -> Ty -> Polar -> Ty -> m Env
module Rules
  ( -- * Helper judgments
    isEvar, inst
    -- * Subtyping judgment (single ssub with Polar)
  , ssub
  ) where

import Prelude hiding ((>>=), (>>), return)
import TypedRedex hiding (fresh, fresh2, fresh3, fresh4, fresh5, fresh6, ground, lift1, lift2, lift3, neg)
import TypedRedex.Nominal.Prelude
import TypedRedex.Nominal.Hash (RedexHash)
import TypedRedex.Interp.Subst (RedexFresh(..))
import TypedRedex.DSL.Moded
  ( Mode(..), T(..)
  , AppliedM(..), MJudgment2, MJudgment3, MJudgment4, MJudgment6, In, Out
  , defJudge2, defJudge3, defJudge4, defJudge6, ModedRule(..)
  , fresh, fresh2, fresh3, fresh4, fresh5, fresh6, prem, concl
  , ground, Union
  , return, (>>=), (>>)
  , (===), (=/=)
  )

import Syntax

--------------------------------------------------------------------------------
-- Type constraint
--------------------------------------------------------------------------------

type PolyRel rel = (RedexFresh rel, RedexEval rel, RedexNeg rel, RedexHash rel)

--------------------------------------------------------------------------------
-- isEvar: Check if type variable is existential in environment
--------------------------------------------------------------------------------

isEvar :: PolyRel rel => MJudgment2 rel "isEvar" (In Env) (In TyNom)
isEvar = defJudge2 @"isEvar" $ \rule ->
  [ rule "here" $ do
      (a, env) <- fresh2
      concl $ isEvar (eevar a env) a

  , rule "there-eevar" $ do
      (a, b, env) <- fresh3
      a =/= b
      prem  $ isEvar env a
      concl $ isEvar (eevar b env) a

  , rule "there-euvar" $ do
      (a, b, env) <- fresh3
      a =/= b
      prem  $ isEvar env a
      concl $ isEvar (euvar b env) a

  , rule "there-esvar" $ do
      (a, b, _ty, env) <- fresh4
      a =/= b
      prem  $ isEvar env a
      concl $ isEvar (esvar b _ty env) a

  , rule "there-etrm" $ do
      (a, _x, _ty, env) <- fresh4
      prem  $ isEvar env a
      concl $ isEvar (etrm _x _ty env) a
  ]

isSvar :: PolyRel rel => MJudgment3 rel "isSvar" (In Env) (In TyNom) (In Ty)
isSvar = defJudge3 @"isSvar" $ \rule ->
  [ rule "here" $ do
      (a, env, ty) <- fresh3
      concl $ isSvar (esvar a ty env) a ty

  , rule "there-esvar" $ do
      (a, b, _tyB, ty, env) <- fresh5
      a =/= b
      prem $ isSvar env a ty
      concl $ isSvar (esvar b _tyB env) a ty

  , rule "there-euvar" $ do
      (a, b, ty, env) <- fresh4
      a =/= b
      prem $ isSvar env a ty
      concl $ isSvar (euvar b env) a ty
  
  , rule "there-eevar" $ do
      (a, b, ty, env) <- fresh4
      a =/= b
      prem $ isSvar env a ty
      concl $ isSvar (eevar b env) a ty
  
  , rule "there-etrm" $ do
      (a, _x, _tyX, ty, env) <- fresh5
      prem $ isSvar env a ty
      concl $ isSvar (etrm _x _tyX env) a ty

  ]

--------------------------------------------------------------------------------
-- inst: Instantiate existential variable
--------------------------------------------------------------------------------

inst :: PolyRel rel => MJudgment4 rel "inst" (In Env) (In TyNom) (In Ty) (Out Env)
inst = defJudge4 @"inst" $ \rule ->
  [ rule "inst-here" $ do
      (a, ty, env) <- fresh3
      concl $ inst (eevar a env) a ty (esvar a ty env)

  , rule "inst-skip-eevar" $ do
      (a, b, ty, env, env') <- fresh5
      concl $ inst (eevar b env) a ty (eevar b env')
      prem $ inst env a ty env'

  , rule "inst-skip-euvar" $ do
      (a, b, ty, env, env') <- fresh5
      concl $ inst (euvar b env) a ty (euvar b env')
      prem $ inst env a ty env'

  , rule "inst-skip-esvar" $ do
      (a, b, tyB, ty, env, env') <- fresh6
      concl $ inst (esvar b tyB env) a ty (esvar b tyB env')
      prem $ inst env a ty env'

  , rule "inst-skip-etrm" $ do
      (a, x, tyX, ty, env, env') <- fresh6
      concl $ inst (etrm x tyX env) a ty (etrm x tyX env')
      prem $ inst env a ty env'
  ]

--------------------------------------------------------------------------------
-- ssub: Polarized subtyping (single judgment with Polar argument)
--------------------------------------------------------------------------------


flipPolar :: PolyRel rel => MJudgment2 rel "flipPolar" (In Polar) (Out Polar)
flipPolar = defJudge2 @"flipPolar" $ \rule ->
  [ rule "pos" $ concl $ flipPolar pos neg
  , rule "neg" $ concl $ flipPolar neg pos
  ]

ssub :: PolyRel rel => MJudgment6 rel "ssub" (In Env) (In Env) (In Ty) (In Polar) (In Ty) (Out Env)
ssub = defJudge6 @"ssub" $ \rule ->
  [ rule "int" $ do
      (env, senv, p) <- fresh3
      concl $ ssub env senv tint p tint senv

  , rule "bool" $ do
      (env, senv, p) <- fresh3
      concl $ ssub env senv tbool p tbool senv

  , rule "mvar-l" $ do
      (env, senv, a, ty, senv') <- fresh5
      prem $ isEvar senv a
      prem $ inst senv a ty senv'
      concl $ ssub env senv (tvar a) pos ty senv'

  , rule "svar-l" $ do
      (env, senv, a, ty) <- fresh4
      prem $ isSvar senv a ty
      concl $ ssub env senv (tvar a) pos ty senv

  , -- [S-MVar-R]: (env, senv) |- ty ≤- a -| senv' when ^a ∈ senv
    rule "mvar-r" $ do
      (env, senv, a, ty, senv') <- fresh5
      prem $ isEvar senv a
      prem $ inst senv a ty senv'
      concl $ ssub env senv ty neg (tvar a) senv'

  , -- [S-Arr]: (env, senv) |- (ty1 -> ty2) ≤ (ty3 -> ty4) -| senv''
    rule "arr" $ do
      (env, senv, ty1, ty2, ty3) <- fresh5
      (p, p') <- fresh2
      (ty4, senv1, senv2) <- fresh3
      prem $ flipPolar p p'
      prem $ ssub env senv ty3 p' ty1 senv1
      prem $ ssub env senv1 ty2 p ty4 senv2
      concl $ ssub env senv (tarr ty1 ty2) p (tarr ty3 ty4) senv2
  ]
