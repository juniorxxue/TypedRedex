{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RebindableSyntax #-}

-- | Polarized subtyping rules matching the Poly design.
module PolyWeak.Rules
  ( flipPolar
  , lookupTmVar
  , lookupUvar
  , lookupBoundVar
  , glb
  , lub
  , updateUpper
  , updateLower
  , splittable
  , splitEnv
  , unsplitEnv
  , inst
  , instP
  , ssub
  , sub
  , tySubst
  , infer
  ) where

import Data.String (fromString)
import Prelude hiding ((>>=), (>>), return)
import qualified Prelude as P
import TypedRedex.DSL hiding (neg, var)
import TypedRedex.Nominal.Bind (bind)
import TypedRedex.Nominal.Prelude (Nom, TyNom)
import TypedRedex.Pretty ((<+>))

import PolyWeak.Syntax

--------------------------------------------------------------------------------
-- Type constraints
--------------------------------------------------------------------------------

flipPolar :: Judgment "flipPolar" '[I, O] '[Polar, Polar]
flipPolar = judgment $
  format (\p p' -> p <+> " is flipped to " <+> p')
  P.>> rules
    [ rule "pos" $ do
        concl $ flipPolar pos neg
    , rule "neg" $ do
        concl $ flipPolar neg pos
    ]

lookupTmVar :: Judgment "lookupVar" '[I, I, O] '[Env, Nom, Ty]
lookupTmVar = judgment $
  format (\env x ty -> env <+> " |- " <+> x <+> " : " <+> ty)
  P.>> rules
    [ rule "here" $ do
        (x, ty, env) <- fresh
        concl $ lookupTmVar (etrm x ty env) x ty

    , rule "skip-trm" $ do
        (x, y, ty, ty', env) <- fresh
        guard $ x =/= y
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

lookupUvar :: Judgment "lookupUvar" '[I, I] '[Env, TyNom]
lookupUvar = judgment $
  format (\env a -> env <+> " |- " <+> a)
  P.>> rules
    [ rule "here" $ do
        (a, env) <- fresh
        concl $ lookupUvar (euvar a env) a

    , rule "skip-trm" $ do
        (a, x, ty, env) <- fresh
        prem  $ lookupUvar env a
        concl $ lookupUvar (etrm x ty env) a

    , rule "skip-uvar" $ do
        (a, b, env) <- fresh
        guard $ a =/= b
        prem  $ lookupUvar env a
        concl $ lookupUvar (euvar b env) a

    , rule "skip-bound" $ do
        (a, b, tyL, tyU, env) <- fresh
        prem  $ lookupUvar env a
        concl $ lookupUvar (ebound tyL b tyU env) a
    ]

lookupBoundVar :: Judgment "lookupBoundVar" '[I, I, O, O] '[Env, TyNom, Ty, Ty]
lookupBoundVar = judgment $
  format (\env a tyL tyU -> env <+> " |- " <+> tyL <+> " <: " <+> a <+> " <: " <+> tyU)
  P.>> rules
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
        guard $ a =/= b
        prem  $ lookupBoundVar env a tyL tyU
        concl $ lookupBoundVar (ebound tyL' b tyU' env) a tyL tyU
    ]

glb :: Judgment "glb" '[I, I, O] '[Ty, Ty, Ty]
glb = judgment $
  format (\ty1 ty2 ty3 -> ty1 <+> " /\\ " <+> ty2 <+> " = " <+> ty3)
  P.>> rules
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
        prem  $ lub tyA tyC tyAC
        prem  $ glb tyB tyD tyBD
        concl $ glb (tarr tyA tyB) (tarr tyC tyD) (tarr tyAC tyBD)
    ]

lub :: Judgment "lub" '[I, I, O] '[Ty, Ty, Ty]
lub = judgment $
  format (\ty1 ty2 ty3 -> ty1 <+> " \\/ " <+> ty2 <+> " = " <+> ty3)
  P.>> rules
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
        prem  $ glb tyA tyC tyAC
        prem  $ lub tyB tyD tyBD
        concl $ lub (tarr tyA tyB) (tarr tyC tyD) (tarr tyAC tyBD)
    ]

updateUpper :: Judgment "updateUpper" '[I, I, I, O] '[Env, TyNom, Ty, Env]
updateUpper = judgment $
  format (\env a ty env' -> env <+> "[" <+> a <+> " upper &= " <+> ty <+> "] = " <+> env')
  P.>> rules
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
        guard $ a =/= b
        prem  $ updateUpper env a tyNew env'
        concl $ updateUpper (ebound tyL' b tyU' env) a tyNew (ebound tyL' b tyU' env')
    ]

updateLower :: Judgment "updateLower" '[I, I, I, O] '[Env, TyNom, Ty, Env]
updateLower = judgment $
  format (\env a ty env' -> env <+> "[" <+> a <+> " lower \\//= " <+> ty <+> "] = " <+> env')
  P.>> rules
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
        guard $ a =/= b
        prem  $ updateLower env a tyNew env'
        concl $ updateLower (ebound tyL' b tyU' env) a tyNew (ebound tyL' b tyU' env')
    ]

splittable :: Judgment "splittable" '[I, I, O, O, O, O] '[Ty, Ty, Ty, Ty, Ty, Ty]
splittable = judgment $
  format (\tyL tyU tyC tyA tyB tyD ->
    tyL <+> " <: " <+> tyU <+> " splittable into " <+>
    tyC <+> ", " <+> tyA <+> " -> " <+> tyB <+> ", " <+> tyD)
  P.>> rules
    [ rule "arr" $ do
        (tyA, tyB, tyC, tyD) <- fresh
        concl $ splittable (tarr tyA tyB) (tarr tyC tyD) tyC tyA tyB tyD
    ]

splitEnv :: Judgment "splitEnv" '[I, I, O, O, O] '[Env, TyNom, Env, TyNom, TyNom]
splitEnv = judgment $
  format (\env a env' b c ->
    env <+> "[" <+> a <+> " ~~> " <+> b <+> " -> " <+> c <+> "] = " <+> env')
  P.>> rules
    [ rule "split" $ do
        (a, env) <- fresh
        (tyL, tyU) <- fresh
        (tyUA, tyLA, tyLB, tyUB) <- fresh
        b <- freshName
        c <- freshName
        prem  $ lookupBoundVar env a tyL tyU
        prem  $ splittable tyL tyU tyUA tyLA tyLB tyUB
        concl $ splitEnv env a (ebound tyUA b tyLA (ebound tyLB c tyUB env)) b c
    ]

unsplitEnv :: Judgment "unsplitEnv" '[I, I, I, O, O] '[Env, TyNom, TyNom, TyNom, Env]
unsplitEnv = judgment $
  format (\env b c a env' ->
    env <+> "[" <+> b <+> " -> " <+> c <+> " ~~> " <+> a <+> "] = " <+> env')
  P.>> rules
    [ rule "unsplit" $ do
        (b, c, env) <- fresh
        (tyUA, tyLA, tyLB, tyUB) <- fresh
        a <- freshName
        prem  $ lookupBoundVar env b tyUA tyLA
        prem  $ lookupBoundVar env c tyLB tyUB
        concl $ unsplitEnv env b c a (ebound (tarr tyLA tyLB) a (tarr tyUA tyUB) env)
    ]


inst :: Judgment "inst" '[I, I, I, I, O] '[Ty, TyNom, Ty, Ty, Ty]
inst = judgment $
  format (\tyL a tyU tyC tyR -> "[" <+> tyL <+> "<:" <+> a <+> "<:" <+> tyU <+> "]" <+> tyC <+> " = " <+> tyR)
  P.>> rules
    [ rule "inst" $ do
        (tyL, a, tyU, tyC, tyR) <- fresh
        prem  $ instP tyL a tyU pos tyC tyR
        concl $ inst tyL a tyU tyC tyR
    ]

instP :: Judgment "instP" '[I, I, I, I, I, O] '[Ty, TyNom, Ty, Polar, Ty, Ty]
instP = judgment $
  format (\tyL a tyU p tyC tyR -> "[" <+> tyL <+> "<:" <+> a <+> "<:" <+> tyU <+> "]" <+> p <+> " " <+> tyC <+> " = " <+> tyR)
  P.>> rules
    [ rule "var-pos" $ do
        (tyL, a, tyU) <- fresh
        concl $ instP tyL a tyU pos (tvar a) tyU

    , rule "var-neg" $ do
        (tyL, a, tyU) <- fresh
        concl $ instP tyL a tyU neg (tvar a) tyL

    , rule "var-other" $ do
        (tyL, a, tyU, p, b) <- fresh
        guard $ a =/= b
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
        prem  $ instP tyL a tyU p' tyA tyA'
        prem  $ instP tyL a tyU p tyB tyB'
        concl $ instP tyL a tyU p (tarr tyA tyB) (tarr tyA' tyB')

    , rule "forall" $ do
        (tyL, a, tyU, p) <- fresh
        (tyBody, tyBody') <- fresh
        b <- freshName
        guard $ a =/= b
        prem  $ instP tyL a tyU p tyBody tyBody'
        concl $ instP tyL a tyU p (tforall b tyBody) (tforall b tyBody')
    ]

ssub :: Judgment "ssub" '[I, I, I, I, O] '[Env, Ty, Polar, Ty, Env]
ssub = judgment $
  format (\env1 ty1 p ty2 env2 -> env1 <+> " |- " <+> ty1 <+> " " <+> p <+> " " <+> ty2 <+> " |- " <+> env2)
  P.>> rules
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
        (tyA, tyB) <- fresh
        a <- freshName
        prem  $ ssub (euvar a env1) tyA p tyB (euvar a env2)
        concl $ ssub env1 (tforall a tyA) p (tforall a tyB) env2
    ]

sub :: Judgment "sub" '[I, I, I, O, O] '[Env, Ty, Context, Env, Ty]
sub = judgment $
  format (\env1 ty1 ctx env2 ty2 ->
    env1 <+> " |- " <+> ty1 <+> " <: " <+> ctx <+> " -| " <+> env2 <+> " ~> " <+> ty2)
  P.>> rules
    [ rule "empty" $ do
        (env, ty) <- fresh
        concl $ sub env ty cempty env ty

    , rule "type" $ do
        (env1, env2, tyA, tyB) <- fresh
        prem  $ ssub env1 tyA pos tyB env2
        concl $ sub env1 tyA (ctype tyB) env2 tyB

    , rule "forallL" $ do
        (tyA, tyB, tyC, tyD) <- fresh
        (a, env1, env2) <- fresh
        (tm, ctx, instTy) <- fresh
        prem  $ sub (ebound tbot a ttop env1) tyA (ctm tm ctx) (ebound tyC a tyD env2) tyB
        prem  $ inst tyC a tyD tyB instTy
        concl $ sub env1 (tforall a tyA) (ctm tm ctx) env2 instTy

    , rule "term" $ do
        (env1, env2, env3) <- fresh
        (tyA, tyB, tyD, tyA') <- fresh
        (ctx, tm) <- fresh
        prem  $ infer env1 (ctype tyA) tm tyA' env2
        prem  $ sub env2 tyB ctx env3 tyD
        concl $ sub env1 (tarr tyA tyB) (ctm tm ctx) env3 (tarr tyA' tyD)

    -- , rule "svar" $ do
    --     (tyA, tyB, tyC) <- fresh
    --     (env1, env2) <- fresh
    --     (a, ctx) <- fresh
    --     prem  $ lookupBoundVar env1 a tyA tyB
    --     prem  $ sub env1 tyB ctx env2 tyC
    --     concl $ sub env1 (tvar a) ctx env2 tyC
    ]

tySubst :: Judgment "tySubst" '[I, I, I, O] '[Ty, TyNom, Ty, Ty]
tySubst = judgment $
  format (\body a repl res -> "[" <+> repl <+> "/" <+> a <+> "]" <+> body <+> " = " <+> res)
  P.>> rules
    [ rule "subst-int" $ do
        (a, ty) <- fresh
        concl $ tySubst tint a ty tint

    , rule "subst-bool" $ do
        (a, ty) <- fresh
        concl $ tySubst tbool a ty tbool

    , rule "subst-top" $ do
        (a, ty) <- fresh
        concl $ tySubst ttop a ty ttop

    , rule "subst-bot" $ do
        (a, ty) <- fresh
        concl $ tySubst tbot a ty tbot

    , rule "subst-var-hit" $ do
        (a, ty) <- fresh
        concl $ tySubst (tvar a) a ty ty

    , rule "subst-var-miss" $ do
        (a, b, ty) <- fresh
        concl $ tySubst (tvar b) a ty (tvar b)
        guard $ a =/= b

    , rule "subst-arr" $ do
        (t1, t2, a, ty, r1, r2) <- fresh
        concl $ tySubst (tarr t1 t2) a ty (tarr r1 r2)
        prem  $ tySubst t1 a ty r1
        prem  $ tySubst t2 a ty r2

    , rule "subst-forall" $ do
        (a, ty, body'') <- fresh
        b <- freshName
        body <- fresh
        concl $ tySubst (tforall b body) a ty (tforall b body'')
        prem  $ tySubst body a ty body''
    ]

infer :: Judgment "infer" '[I, I, I, O, O] '[Env, Context, Tm, Ty, Env]
infer = judgment $
  format (\env1 ctx tm ty env2 -> env1 <+> " |- " <+> ctx <+> " => " <+> tm <+> " => " <+> ty <+> " |- " <+> env2)
  P.>> rules
    [ rule "lit" $ do
        (n, env) <- fresh
        concl $ infer env cempty (lit n) tint env

    , rule "var" $ do
        (x, ty, env) <- fresh
        prem  $ lookupTmVar env x ty
        concl $ infer env cempty (var x) ty env

    , rule "ann" $ do
        (tm, ty, env1, env2) <- fresh
        prem  $ infer env1 (ctype ty) tm ty env2
        concl $ infer env1 cempty (ann tm ty) ty env2

    , rule "lam1" $ do
        (x, tm, env1, env2) <- fresh
        (ty1, ty2, ty3) <- fresh
        prem  $ infer (etrm x ty1 env1) (ctype ty2) tm ty3 (etrm x ty1 env2)
        concl $ infer env1 (ctype (tarr ty1 ty2)) (lam x tm) (tarr ty1 ty3) env2

    , rule "lam2" $ do
        (x, tm1, tm2, env1, ctx, env2, env3) <- fresh
        (ty1, ty2) <- fresh
        prem  $ infer env1 cempty tm2 ty1 env2
        prem  $ infer (etrm x ty1 env1) ctx tm1 ty2 (etrm x ty1 env3)
        concl $ infer env1 (ctm tm2 ctx) (lam x tm1) (tarr ty1 ty2) env3

    , rule "lam3" $ do
        (x, tm, env1, env2, env3, env4) <- fresh
        (ty1, ty2, ty3) <- fresh
        (a, b, c) <- fresh
        prem  $ lookupBoundVar env1 a ty1 ty2
        prem  $ splitEnv env1 a env2 b c
        prem  $ infer (etrm x (tvar b) env2) (ctype (tvar c)) tm ty3 (etrm x (tvar b) env3)
        prem  $ unsplitEnv env3 a b c env4
        concl $ infer env1 (ctype (tvar a)) (lam x tm) (tarr ty1 ty3) env4

    , rule "tlam1" $ do
        (a, tm, env1, env2, ty) <- fresh
        prem  $ infer (euvar a env1) cempty tm ty (euvar a env2)
        concl $ infer env1 cempty (tlam a tm) (tforall a ty) env2

    , rule "tlam2" $ do
        (a, tm, env1, ty1, ty2, env2) <- fresh
        prem  $ infer (euvar a env1) (ctype ty2) tm ty1 (euvar a env2)
        concl $ infer env1 (ctype (tforall a ty2)) (tlam a tm) (tforall a ty1) env2

    , rule "app" $ do
        (tm1, tm2, env1, ctx, env2) <- fresh
        (ty1, ty2) <- fresh
        prem  $ infer env1 (ctm tm2 ctx) tm1 (tarr ty1 ty2) env2
        concl $ infer env1 ctx (app tm1 tm2) ty2 env2

    , rule "tapp" $ do
        (tm, ty2, env1, ctx, env2, env) <- fresh
        (a, ty1, ty3, stTy) <- fresh
        prem  $ infer env1 cempty tm (tforall a ty1) env
        prem  $ tySubst ty1 a ty2 stTy
        prem  $ sub env1 stTy ctx env2 ty3
        concl $ infer env1 ctx (tapp tm ty2) ty3 env2

    , rule "sub" $ do
        (env1, env, env2) <- fresh
        (ctx, g, tyA, tyB) <- fresh
        guard $ ctx =/= cempty
        prem  $ infer env1 cempty g tyA env
        prem  $ sub env1 tyA ctx env2 tyB
        concl $ infer env1 ctx g tyB env2
    ]
