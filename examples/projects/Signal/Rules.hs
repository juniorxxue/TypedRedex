{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RebindableSyntax #-}

-- | Auxiliary judgments for Signal type system.
module Signal.Rules where

import Data.String (fromString)
import Prelude hiding ((>>=), (>>), return)
import qualified Prelude as P
import TypedRedex.DSL hiding (neg, var, ground)
import TypedRedex.Nominal.Prelude (Nom, TyNom)
import TypedRedex.Pretty ((<+>))

import Signal.Syntax

--------------------------------------------------------------------------------
-- Polarity flip
--------------------------------------------------------------------------------

flipPolar :: Judgment "flipPolar" '[I, O] '[Polar, Polar]
flipPolar = judgment $
  format (\p p' -> p <+> " => " <+> p')
  P.>> rules
    [ rule "pos" $ do
        concl $ flipPolar pos neg
    , rule "neg" $ do
        concl $ flipPolar neg pos
    ]

--------------------------------------------------------------------------------
-- Environment concatenation
--------------------------------------------------------------------------------

envConcat :: Judgment "envConcat" '[I, I, O] '[Env, Env, Env]
envConcat = judgment $
  format (\env senv env' -> env <+> " ++ " <+> senv <+> " = " <+> env')
  P.>> rules
    [ rule "empty" $ do
        env <- fresh
        concl $ envConcat env eempty env

    , rule "trm" $ do
        (env, x, ty, senv, env') <- fresh
        prem  $ envConcat env senv env'
        concl $ envConcat env (etrm x ty senv) (etrm x ty env')

    , rule "uvar" $ do
        (env, a, senv, env') <- fresh
        prem  $ envConcat env senv env'
        concl $ envConcat env (euvar a senv) (euvar a env')

    , rule "evar" $ do
        (env, a, senv, env') <- fresh
        prem  $ envConcat env senv env'
        concl $ envConcat env (eevar a senv) (eevar a env')

    , rule "svar" $ do
        (env, a, ty, senv, env') <- fresh
        prem  $ envConcat env senv env'
        concl $ envConcat env (esvar a ty senv) (esvar a ty env')
    ]

--------------------------------------------------------------------------------
-- Term variable lookup
--------------------------------------------------------------------------------

lookupTmVar :: Judgment "lookupTmVar" '[I, I, O] '[Env, Nom, Ty]
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

    , rule "skip-evar" $ do
        (x, a, ty, env) <- fresh
        prem  $ lookupTmVar env x ty
        concl $ lookupTmVar (eevar a env) x ty

    , rule "skip-svar" $ do
        (x, a, ty, ty', env) <- fresh
        prem  $ lookupTmVar env x ty
        concl $ lookupTmVar (esvar a ty' env) x ty
    ]

--------------------------------------------------------------------------------
-- Universal type variable lookup
--------------------------------------------------------------------------------

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

    , rule "skip-evar" $ do
        (a, b, env) <- fresh
        guard $ a =/= b
        prem  $ lookupUvar env a
        concl $ lookupUvar (eevar b env) a

    , rule "skip-svar" $ do
        (a, b, ty, env) <- fresh
        guard $ a =/= b
        prem  $ lookupUvar env a
        concl $ lookupUvar (esvar b ty env) a
    ]

--------------------------------------------------------------------------------
-- Existential type variable lookup (unsolved)
--------------------------------------------------------------------------------

lookupEvar :: Judgment "lookupEvar" '[I, I] '[Env, TyNom]
lookupEvar = judgment $
  format (\env a -> env <+> " |- ^" <+> a)
  P.>> rules
    [ rule "here" $ do
        (a, env) <- fresh
        concl $ lookupEvar (eevar a env) a

    , rule "skip-trm" $ do
        (a, x, ty, env) <- fresh
        prem  $ lookupEvar env a
        concl $ lookupEvar (etrm x ty env) a

    , rule "skip-uvar" $ do
        (a, b, env) <- fresh
        prem  $ lookupEvar env a
        concl $ lookupEvar (euvar b env) a

    , rule "skip-evar" $ do
        (a, b, env) <- fresh
        guard $ a =/= b
        prem  $ lookupEvar env a
        concl $ lookupEvar (eevar b env) a

    , rule "skip-svar" $ do
        (a, b, ty, env) <- fresh
        prem  $ lookupEvar env a
        concl $ lookupEvar (esvar b ty env) a
    ]

--------------------------------------------------------------------------------
-- Solved type variable lookup
--------------------------------------------------------------------------------

lookupSvar :: Judgment "lookupSvar" '[I, I, O] '[Env, TyNom, Ty]
lookupSvar = judgment $
  format (\env a ty -> env <+> " |- " <+> a <+> " = " <+> ty)
  P.>> rules
    [ rule "here" $ do
        (a, ty, env) <- fresh
        concl $ lookupSvar (esvar a ty env) a ty

    , rule "skip-trm" $ do
        (a, x, ty, ty', env) <- fresh
        prem  $ lookupSvar env a ty
        concl $ lookupSvar (etrm x ty' env) a ty

    , rule "skip-uvar" $ do
        (a, b, ty, env) <- fresh
        guard $ a =/= b
        prem  $ lookupSvar env a ty
        concl $ lookupSvar (euvar b env) a ty

    , rule "skip-evar" $ do
        (a, b, ty, env) <- fresh
        guard $ a =/= b
        prem  $ lookupSvar env a ty
        concl $ lookupSvar (eevar b env) a ty

    , rule "skip-svar" $ do
        (a, b, ty, ty', env) <- fresh
        guard $ a =/= b
        prem  $ lookupSvar env a ty
        concl $ lookupSvar (esvar b ty' env) a ty
    ]

--------------------------------------------------------------------------------
-- Instantiation (solve an existential variable)
--------------------------------------------------------------------------------

-- assume it finds a unsolved matching variable
inst :: Judgment "inst" '[I, I, I, O] '[Env, TyNom, Ty, Env]
inst = judgment $
  format (\env a ty env' -> env <+> " [" <+> a <+> " := " <+> ty <+> "] = " <+> env')
  P.>> rules
    [ rule "trm-skip" $ do
        (x, tyX, env, env', a, tyA) <- fresh
        prem  $ inst env a tyA env'
        concl $ inst (etrm x tyX env) a tyA (etrm x tyX env')

    , rule "uvar-skip" $ do
        (b, env, env', a, tyA) <- fresh
        guard $ a =/= b
        prem  $ inst env a tyA env'
        concl $ inst (euvar b env) a tyA (euvar b env')

    , rule "evar" $ do
        (a, env, tyA) <- fresh
        concl $ inst (eevar a env) a tyA (esvar a tyA env)

    , rule "evar-skip" $ do
        (a, b, env, env', tyA) <- fresh
        guard $ a =/= b
        prem  $ inst env a tyA env'
        concl $ inst (eevar b env) a tyA (eevar b env')

    , rule "svar-skip" $ do
        (b, tyB, env, env', a, tyA) <- fresh
        guard $ a =/= b
        prem  $ inst env a tyA env'
        concl $ inst (esvar b tyB env) a tyA (esvar b tyB env')
    ]


open :: Judgment "open" '[I, I] '[Env, Ty]
open = judgment $
  format (\env ty -> env <+> " |-open " <+> ty)
  P.>> rules
    [ rule "var-evar" $ do
        (env, a) <- fresh
        prem  $ lookupEvar env a
        concl $ open env (tvar a)

    , rule "arr-left" $ do
        (env, ty1, ty2) <- fresh
        prem  $ open env ty1
        concl $ open env (tarr ty1 ty2)

    , rule "arr-right" $ do
        (env, ty1, ty2) <- fresh
        prem  $ open env ty2
        concl $ open env (tarr ty1 ty2)

    , rule "forall" $ do
        (env, a, ty) <- fresh
        prem  $ open (euvar a env) ty
        concl $ open env (tforall a ty)
    ]

closed :: Judgment "closed" '[I, I] '[Env, Ty]
closed = judgment $
  format (\env ty -> env <+> " |-closed " <+> ty)
  P.>> rules
    [ rule "int" $ do
        env <- fresh
        concl $ closed env tint

    , rule "bool" $ do
        env <- fresh
        concl $ closed env tbool

    , rule "var-uvar" $ do
        (env, a) <- fresh
        prem  $ lookupUvar env a
        concl $ closed env (tvar a)

    , rule "var-svar" $ do
        (env, a, ty) <- fresh
        prem  $ lookupSvar env a ty
        concl $ closed env (tvar a)

    , rule "arr" $ do
        (env, ty1, ty2) <- fresh
        prem  $ closed env ty1
        prem  $ closed env ty2
        concl $ closed env (tarr ty1 ty2)

    , rule "forall" $ do
        (env, a, ty) <- fresh
        prem  $ closed (euvar a env) ty
        concl $ closed env (tforall a ty)
    ]

ground :: Judgment "ground" '[I, I, O] '[Env, Ty, Ty]
ground = judgment $
  format (\env ty ty' -> " [" <+> env <+> "]" <+> ty <+> " = " <+> ty')
  P.>> rules
    [ rule "int" $ do
        env <- fresh
        concl $ ground env tint tint

    , rule "bool" $ do
        env <- fresh
        concl $ ground env tbool tbool

    , rule "var-uvar" $ do
        (env, a) <- fresh
        prem  $ lookupUvar env a
        concl $ ground env (tvar a) (tvar a)

    , rule "var-svar" $ do
        (env, a, ty) <- fresh
        prem  $ lookupSvar env a ty
        concl $ ground env (tvar a) ty

    , rule "arr" $ do
        (env, ty1, ty2, ty1', ty2') <- fresh
        prem  $ ground env ty1 ty1'
        prem  $ ground env ty2 ty2'
        concl $ ground env (tarr ty1 ty2) (tarr ty1' ty2')

    , rule "forall" $ do
        (env, a, ty, ty') <- fresh
        prem  $ ground (euvar a env) ty ty'
        concl $ ground env (tforall a ty) (tforall a ty')
    ]


ssub :: Judgment "ssub" '[I, I, I, I, O] '[Env, Ty, Polar, Ty, Env]
ssub = judgment $
  format (\env ty1 p ty2 env' ->
    env <+> " |- " <+> ty1 <+> " " <+> p <+> " " <+> ty2 <+> " -| " <+> env')
  P.>> rules
    [ rule "S-Int" $ do
        (env, p) <- fresh
        concl $ ssub env tint p tint env

    , rule "S-Bool" $ do
        (env, p) <- fresh
        concl $ ssub env tbool p tbool env

    , rule "S-Refl" $ do
        (env, a, p) <- fresh
        prem  $ lookupUvar env a
        concl $ ssub env (tvar a) p (tvar a) env

    , rule "S-MVar-L" $ do
        (env, a, tyA, env') <- fresh
        prem  $ lookupEvar env a
        prem  $ inst env a tyA env'
        concl $ ssub env (tvar a) pos tyA env'

    , rule "S-SVar-L" $ do
        (env, a, tyA, tyB) <- fresh
        prem  $ lookupSvar env a tyB
        tyA === tyB
        concl $ ssub env (tvar a) pos tyA env

    , rule "S-MVar-R" $ do
        (env, a, tyA, env') <- fresh
        prem  $ lookupEvar env a
        prem  $ inst env a tyA env'
        concl $ ssub env tyA neg (tvar a) env'

    , rule "S-SVar-R" $ do
        (env, a, tyA, tyB) <- fresh
        prem  $ lookupSvar env a tyB
        tyA === tyB
        concl $ ssub env tyA neg (tvar a) env

    , rule "S-Arr" $ do
        (env, tyA, tyB, tyC, tyD, p, p', env', env'') <- fresh
        prem  $ flipPolar p p'
        prem  $ ssub env tyC p' tyA env'
        prem  $ ssub env' tyB p tyD env''
        concl $ ssub env (tarr tyA tyB) p (tarr tyC tyD) env''

    , rule "S-Forall" $ do
        (env, tyA, tyB, p, env') <- fresh
        a <- freshName
        prem  $ ssub (euvar a env) tyA p tyB (euvar a env')
        concl $ ssub env (tforall a tyA) p (tforall a tyB) env'
    ]

sub :: Judgment "sub" '[I, I, I, O, O, O] '[Env, Ty, Context, Env, Ty, Signal]
sub = judgment $
  format (\env ty ctx env' ty' sig ->
    env <+> " |- " <+> ty <+> " <: " <+> ctx <+> " -| " <+> env' <+> " ~> " <+> ty' <+> " ~> " <+> sig)
    P.>> rules
    [ rule "empty" $ do
        (env, ty) <- fresh
        prem  $ closed env ty
        concl $ sub env ty cempty env ty yes

    , rule "type" $ do
        (env, env', tyA, tyB, tyA') <- fresh
        prem  $ closed env tyA
        prem  $ ground env tyA tyA'
        prem  $ ssub env tyA' neg tyB env'
        concl $ sub env tyA (ctype tyB) env' tyB yes

    , rule "term1" $ do
        (env, env', tyA, tyB, ctx, e, env'', tyD) <- fresh
        prem  $ infer env (ctype tyA) e tyA env' yes
        prem  $ sub env' tyB ctx env'' tyD yes
        concl $ sub env (tarr tyA tyB) (ctm e ctx) env'' (tarr tyA tyD) yes

    , rule "term2" $ do
        (env, env', env'', tyA, tyB, ctx, e, tyB') <- fresh
        prem  $ infer env (ctype tyA) e tyA env' no
        prem  $ sub env tyB ctx env' tyB' yes
        prem  $ closed env' tyA -- it's ok not to ground that early
        prem  $ infer env' (ctype tyA) e tyA env'' yes
        concl $ sub env (tarr tyA tyB) (ctm e ctx) env'' (tarr tyA tyB') yes

    , rule "term3" $ do
        (env, env', env'', tyA, tyB, ctx, e, tyB') <- fresh
        prem  $ infer env (ctype tyA) e tyA env' no
        prem  $ sub env tyB ctx env' tyB' yes
        prem  $ closed env' tyA -- it's ok not to ground that early
        prem  $ infer env' (ctype tyA) e tyA env'' no
        concl $ sub env (tarr tyA tyB) (ctm e ctx) env'' (tarr tyA tyB') no
    ]

infer :: Judgment "infer" '[I, I, I, O, O, O] '[Env, Context, Tm, Ty, Env, Signal]
infer = judgment $
  format (\env1 ctx tm ty env2 sig -> env1 <+> " |- " <+> ctx <+> " => " <+> tm <+> " => " <+> ty <+> " -| " <+> env2 <+> " ~> " <+> sig)
  P.>> rules
    [ rule "int" $ do
        (env, n) <- fresh
        concl $ infer env cempty (lit n) tint env yes

    , rule "var" $ do
        (env, x, ty) <- fresh
        prem  $ lookupTmVar env x ty
        concl $ infer env cempty (var x) ty env yes

    , rule "ann" $ do
        (env, e, tyA) <- fresh
        prem  $ infer env (ctype tyA) e tyA env yes
        concl $ infer env cempty (ann e tyA) tyA env yes

    , rule "abs1" $ do
        (env, x, tyB, tyC, e, tyA) <- fresh
        prem $ closed env tyA
        prem $ ground env tyA (tarr tyB tyC)
        prem $ infer (etrm x tyB env) (ctype tyC) e tyC (etrm x tyB env) yes
        concl $ infer env (ctype tyA) (lam x e) (tarr tyB tyC) env yes

    , rule "abs2" $ do
        (env, x, e, tyA) <- fresh
        prem  $ open env tyA
        concl $ infer env (ctype tyA) (lam x e) tyA env no

    , rule "abs3" $ do
        (env, env', x, e, e2, ctx, tyA, tyB, sig) <- fresh
        prem  $ infer env cempty e2 tyA env yes
        prem  $ infer (etrm x tyA env) ctx e tyB (etrm x tyA env') sig
        concl $ infer env (ctm e2 ctx) (lam x e) (tarr tyA tyB) env' sig

    , rule "app" $ do
        (env, e1, e2, ctx, tyA, tyB, env', sig) <- fresh
        prem  $ infer env (ctm e2 ctx) e1 (tarr tyA tyB) env' sig
        concl $ infer env ctx (app e1 e2) tyB env' sig
    ]