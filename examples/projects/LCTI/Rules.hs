{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RebindableSyntax #-}

module LCTI.Rules
  ( flipPolar
  , envConcat
  , lookupTmVar
  , lookupUvar
  , lookupEvar
  , lookupSvar
  , inst
  , closed
  , open
  , ground
  , ssub
  , inferUncurry
  , sub
  , infers
  , tySubst
  , infer
  ) where

import Data.String (fromString)
import Prelude hiding ((>>=), (>>), return, abs, fst, snd)
import qualified Prelude as P
import TypedRedex.DSL hiding (neg, var, ground)
import TypedRedex.Nominal.Prelude (Nom, TyNom)
import TypedRedex.Pretty ((<+>))

import LCTI.Syntax

--------------------------------------------------------------------------------
-- Helper judgments
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

lookupTmVar :: Judgment "lookupTmVar" '[I, I, O] '[Env, Nom, Ty]
lookupTmVar = judgment $
  format (\env x ty -> env <+> " |- " <+> x <+> " : " <+> ty)
  P.>> rules
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

    , rule "skip-evar" $ do
        (x, a, ty, env) <- fresh
        prem  $ lookupTmVar env x ty
        concl $ lookupTmVar (eevar a env) x ty

    , rule "skip-svar" $ do
        (x, a, ty, ty', env) <- fresh
        prem  $ lookupTmVar env x ty
        concl $ lookupTmVar (esvar a ty' env) x ty
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
        a =/= b
        prem  $ lookupUvar env a
        concl $ lookupUvar (euvar b env) a

    , rule "skip-evar" $ do
        (a, b, env) <- fresh
        prem  $ lookupUvar env a
        concl $ lookupUvar (eevar b env) a

    , rule "skip-svar" $ do
        (a, b, ty, env) <- fresh
        prem  $ lookupUvar env a
        concl $ lookupUvar (esvar b ty env) a
    ]

lookupEvar :: Judgment "lookupEvar" '[I, I] '[Env, TyNom]
lookupEvar = judgment $
  format (\env a -> env <+> " |- " <+> a <+> "^")
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
        a =/= b
        prem  $ lookupEvar env a
        concl $ lookupEvar (eevar b env) a

    , rule "skip-svar" $ do
        (a, b, ty, env) <- fresh
        prem  $ lookupEvar env a
        concl $ lookupEvar (esvar b ty env) a
    ]

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
        prem  $ lookupSvar env a ty
        concl $ lookupSvar (euvar b env) a ty

    , rule "skip-evar" $ do
        (a, b, ty, env) <- fresh
        prem  $ lookupSvar env a ty
        concl $ lookupSvar (eevar b env) a ty

    , rule "skip-svar" $ do
        (a, b, ty, ty', env) <- fresh
        a =/= b
        prem  $ lookupSvar env a ty
        concl $ lookupSvar (esvar b ty' env) a ty
    ]

inst :: Judgment "inst" '[I, I, I, O] '[Env, TyNom, Ty, Env]
inst = judgment $
  format (\env a ty env' -> env <+> " [" <+> a <+> " := " <+> ty <+> "] = " <+> env')
  P.>> rules
    [ rule "trm" $ do
        (x, tyX, env, env', a, tyA) <- fresh
        prem  $ inst env a tyA env'
        concl $ inst (etrm x tyX env) a tyA (etrm x tyX env')

    , rule "uvar" $ do
        (b, env, env', a, tyA) <- fresh
        prem  $ inst env a tyA env'
        concl $ inst (euvar b env) a tyA (euvar b env')

    , rule "evar-hit" $ do
        (a, env, tyA) <- fresh
        concl $ inst (eevar a env) a tyA (esvar a tyA env)

    , rule "evar-miss" $ do
        (a, b, env, env', tyA) <- fresh
        a =/= b
        prem  $ inst env a tyA env'
        concl $ inst (eevar b env) a tyA (eevar b env')

    , rule "svar" $ do
        (b, tyB, env, env', a, tyA) <- fresh
        prem  $ inst env a tyA env'
        concl $ inst (esvar b tyB env) a tyA (esvar b tyB env')
    ]

tyZipEq :: Judgment "tyZipEq" '[I, I] '[ [Ty], [Ty] ]
tyZipEq = judgment $
  format (\xs ys -> xs <+> " ~= " <+> ys)
  P.>> rules
    [ rule "zip-nil-left" $ do
        ys <- fresh
        concl $ tyZipEq lnil ys

    , rule "zip-nil-right" $ do
        xs <- fresh
        concl $ tyZipEq xs lnil

    , rule "zip-cons" $ do
        (x, xs, y, ys) <- fresh
        x === y
        prem  $ tyZipEq xs ys
        concl $ tyZipEq (lcons x xs) (lcons y ys)
    ]

splitAnnList :: Judgment "splitAnnList" '[I, O, O] '[ [(Nom, Ty)], [Nom], [Ty] ]
splitAnnList = judgment $
  format (\anns xs tys -> anns <+> " => " <+> xs <+> ", " <+> tys)
  P.>> rules
    [ rule "split-nil" $ do
        concl $ splitAnnList lnil lnil lnil

    , rule "split-cons" $ do
        (x, ty, rest, xs, tys) <- fresh
        prem  $ splitAnnList rest xs tys
        concl $ splitAnnList (lcons (tup x ty) rest) (lcons x xs) (lcons ty tys)
    ]

extendEnvZip :: Judgment "extendEnvZip" '[I, I, I, O] '[ [Nom], [Ty], Env, Env ]
extendEnvZip = judgment $
  format (\xs tys env env' -> env <+> " + " <+> xs <+> " : " <+> tys <+> " = " <+> env')
  P.>> rules
    [ rule "zip-nil-names" $ do
        (tys, env) <- fresh
        concl $ extendEnvZip lnil tys env env

    , rule "zip-nil-types" $ do
        (xs, env) <- fresh
        concl $ extendEnvZip xs lnil env env

    , rule "zip-cons" $ do
        (x, xs, ty, tys, env, env') <- fresh
        prem  $ extendEnvZip xs tys (etrm x ty env) env'
        concl $ extendEnvZip (lcons x xs) (lcons ty tys) env env'
    ]

inferList :: Judgment "inferList" '[I, I, O] '[Env, [Tm], [Ty]]
inferList = judgment $
  format (\env tms tys -> env <+> " |- " <+> tms <+> " => " <+> tys)
  P.>> rules
    [ rule "infer-nil" $ do
        env <- fresh
        concl $ inferList env lnil lnil

    , rule "infer-cons" $ do
        (env, tm, tms, ty, tys) <- fresh
        prem  $ infer env cempty tm ty
        prem  $ inferList env tms tys
        concl $ inferList env (lcons tm tms) (lcons ty tys)
    ]

inferZip :: Judgment "inferZip" '[I, I, I] '[Env, [Ty], [Tm]]
inferZip = judgment $
  format (\env tys tms -> env <+> " |- " <+> tys <+> " <~ " <+> tms)
  P.>> rules
    [ rule "zip-nil-types" $ do
        (env, tms) <- fresh
        concl $ inferZip env lnil tms

    , rule "zip-nil-terms" $ do
        (env, tys) <- fresh
        concl $ inferZip env tys lnil

    , rule "zip-cons" $ do
        (env, ty, tys, tm, tms, ty') <- fresh
        prem  $ infer env (cfulltype ty) tm ty'
        prem  $ inferZip env tys tms
        concl $ inferZip env (lcons ty tys) (lcons tm tms)
    ]

inferUncurryList :: Judgment "inferUncurryList" '[I, I, I, I, O, O] '[Env, Env, [Ty], [Tm], Env, [Ty]]
inferUncurryList = judgment $
  format (\env senv tys tms senv' tys' ->
    env <+> "; " <+> senv <+> " |- " <+> tys <+> " <~ " <+> tms <+> " => " <+> senv' <+> ", " <+> tys')
  P.>> rules
    [ rule "zip-nil-types" $ do
        (env, senv, tms) <- fresh
        concl $ inferUncurryList env senv lnil tms senv lnil

    , rule "zip-nil-terms" $ do
        (env, senv, tys) <- fresh
        concl $ inferUncurryList env senv tys lnil senv lnil

    , rule "zip-cons" $ do
        (env, senv, ty, tys, tm, tms, senv', senv'', ty', tys') <- fresh
        prem  $ inferUncurry env senv ty tm senv' ty'
        prem  $ inferUncurryList env senv' tys tms senv'' tys'
        concl $ inferUncurryList env senv (lcons ty tys) (lcons tm tms) senv'' (lcons ty' tys')
    ]

closedList :: Judgment "closedList" '[I, I] '[Env, [Ty]]
closedList = judgment $
  format (\env tys -> env <+> " |- closed " <+> tys)
  P.>> rules
    [ rule "closed-nil" $ do
        env <- fresh
        concl $ closedList env lnil

    , rule "closed-cons" $ do
        (env, ty, tys) <- fresh
        prem  $ closed env ty
        prem  $ closedList env tys
        concl $ closedList env (lcons ty tys)
    ]

openList :: Judgment "openList" '[I, I] '[Env, [Ty]]
openList = judgment $
  format (\env tys -> env <+> " |- open " <+> tys)
  P.>> rules
    [ rule "open-head" $ do
        (env, ty, tys) <- fresh
        prem  $ open env ty
        concl $ openList env (lcons ty tys)

    , rule "open-tail" $ do
        (env, ty, tys) <- fresh
        prem  $ openList env tys
        concl $ openList env (lcons ty tys)
    ]

groundList :: Judgment "groundList" '[I, I, O] '[Env, [Ty], [Ty]]
groundList = judgment $
  format (\env tys tys' -> env <+> " |- " <+> tys <+> " ~~> " <+> tys')
  P.>> rules
    [ rule "ground-nil" $ do
        env <- fresh
        concl $ groundList env lnil lnil

    , rule "ground-cons" $ do
        (env, ty, tys, ty', tys') <- fresh
        prem  $ ground env ty ty'
        prem  $ groundList env tys tys'
        concl $ groundList env (lcons ty tys) (lcons ty' tys')
    ]

tySubstList :: Judgment "tySubstList" '[I, I, I, O] '[ [Ty], TyNom, Ty, [Ty] ]
tySubstList = judgment $
  format (\tys a repl tys' -> "[" <+> repl <+> "/" <+> a <+> "] " <+> tys <+> " = " <+> tys')
  P.>> rules
    [ rule "subst-nil" $ do
        (a, repl) <- fresh
        concl $ tySubstList lnil a repl lnil

    , rule "subst-cons" $ do
        (ty, tys, a, repl, ty', tys') <- fresh
        prem  $ tySubst ty a repl ty'
        prem  $ tySubstList tys a repl tys'
        concl $ tySubstList (lcons ty tys) a repl (lcons ty' tys')
    ]

genericConsumer :: Judgment "genericConsumer" '[I] '[Tm]
genericConsumer = judgment $
  format (\tm -> "consumer " <+> tm)
  P.>> rules
    [ rule "lit-int" $ do
        n <- fresh
        concl $ genericConsumer (litInt n)

    , rule "lit-bool" $ do
        b <- fresh
        concl $ genericConsumer (litBool b)

    , rule "var" $ do
        x <- fresh
        concl $ genericConsumer (var x)

    , rule "ann" $ do
        (tm, ty) <- fresh
        concl $ genericConsumer (ann tm ty)

    , rule "tabs" $ do
        (a, tm) <- fresh
        concl $ genericConsumer (tabs a tm)
    ]

nonEmptyContext :: Judgment "nonEmptyContext" '[I] '[Context]
nonEmptyContext = judgment $
  format (\ctx -> "nonempty " <+> ctx)
  P.>> rules
    [ rule "type" $ do
        ty <- fresh
        concl $ nonEmptyContext (cfulltype ty)

    , rule "term" $ do
        (tm, ctx) <- fresh
        concl $ nonEmptyContext (cterm tm ctx)

    , rule "uncurry" $ do
        (tms, ctx) <- fresh
        concl $ nonEmptyContext (cuncurry tms ctx)

    , rule "fst" $ do
        ctx <- fresh
        concl $ nonEmptyContext (cfst ctx)

    , rule "snd" $ do
        ctx <- fresh
        concl $ nonEmptyContext (csnd ctx)
    ]

--------------------------------------------------------------------------------
-- Closed/Open/Ground
--------------------------------------------------------------------------------

closed :: Judgment "closed" '[I, I] '[Env, Ty]
closed = judgment $
  format (\env ty -> env <+> " |- closed " <+> ty)
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

    , rule "uncurry" $ do
        (env, tys, ty) <- fresh
        prem  $ closedList env tys
        prem  $ closed env ty
        concl $ closed env (tuncurry tys ty)

    , rule "list" $ do
        (env, ty) <- fresh
        prem  $ closed env ty
        concl $ closed env (tlist ty)

    , rule "prod" $ do
        (env, ty1, ty2) <- fresh
        prem  $ closed env ty1
        prem  $ closed env ty2
        concl $ closed env (tprod ty1 ty2)

    , rule "st" $ do
        (env, ty1, ty2) <- fresh
        prem  $ closed env ty1
        prem  $ closed env ty2
        concl $ closed env (tst ty1 ty2)
    ]

open :: Judgment "open" '[I, I] '[Env, Ty]
open = judgment $
  format (\env ty -> env <+> " |- open " <+> ty)
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

    , rule "uncurry" $ do
        (env, tys, ty) <- fresh
        prem  $ openList env tys
        concl $ open env (tuncurry tys ty)

    , rule "uncurry-res" $ do
        (env, tys, ty) <- fresh
        prem  $ open env ty
        concl $ open env (tuncurry tys ty)

    , rule "list" $ do
        (env, ty) <- fresh
        prem  $ open env ty
        concl $ open env (tlist ty)

    , rule "prod-left" $ do
        (env, ty1, ty2) <- fresh
        prem  $ open env ty1
        concl $ open env (tprod ty1 ty2)

    , rule "prod-right" $ do
        (env, ty1, ty2) <- fresh
        prem  $ open env ty2
        concl $ open env (tprod ty1 ty2)

    , rule "st-left" $ do
        (env, ty1, ty2) <- fresh
        prem  $ open env ty1
        concl $ open env (tst ty1 ty2)

    , rule "st-right" $ do
        (env, ty1, ty2) <- fresh
        prem  $ open env ty2
        concl $ open env (tst ty1 ty2)
    ]

ground :: Judgment "ground" '[I, I, O] '[Env, Ty, Ty]
ground = judgment $
  format (\env ty ty' -> env <+> " |- " <+> ty <+> " ~~> " <+> ty')
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

    , rule "uncurry" $ do
        (env, tys, ty, tys', ty') <- fresh
        prem  $ groundList env tys tys'
        prem  $ ground env ty ty'
        concl $ ground env (tuncurry tys ty) (tuncurry tys' ty')

    , rule "list" $ do
        (env, ty, ty') <- fresh
        prem  $ ground env ty ty'
        concl $ ground env (tlist ty) (tlist ty')

    , rule "prod" $ do
        (env, ty1, ty2, ty1', ty2') <- fresh
        prem  $ ground env ty1 ty1'
        prem  $ ground env ty2 ty2'
        concl $ ground env (tprod ty1 ty2) (tprod ty1' ty2')

    , rule "st" $ do
        (env, ty1, ty2, ty1', ty2') <- fresh
        prem  $ ground env ty1 ty1'
        prem  $ ground env ty2 ty2'
        concl $ ground env (tst ty1 ty2) (tst ty1' ty2')
    ]

--------------------------------------------------------------------------------
-- Substitution
--------------------------------------------------------------------------------

tySubst :: Judgment "tySubst" '[I, I, I, O] '[Ty, TyNom, Ty, Ty]
tySubst = judgment $
  format (\body a repl res -> "[" <+> repl <+> "/" <+> a <+> "] " <+> body <+> " = " <+> res)
  P.>> rules
    [ rule "subst-int" $ do
        (a, ty) <- fresh
        concl $ tySubst tint a ty tint

    , rule "subst-bool" $ do
        (a, ty) <- fresh
        concl $ tySubst tbool a ty tbool

    , rule "subst-var-hit" $ do
        (a, ty) <- fresh
        concl $ tySubst (tvar a) a ty ty

    , rule "subst-var-miss" $ do
        (a, b, ty) <- fresh
        a =/= b
        concl $ tySubst (tvar b) a ty (tvar b)

    , rule "subst-arr" $ do
        (t1, t2, a, ty, r1, r2) <- fresh
        prem  $ tySubst t1 a ty r1
        prem  $ tySubst t2 a ty r2
        concl $ tySubst (tarr t1 t2) a ty (tarr r1 r2)

    , rule "subst-forall" $ do
        (a, ty, body'') <- fresh
        b <- freshName
        body <- fresh
        concl $ tySubst (tforall b body) a ty (tforall b body'')
        prem  $ tySubst body a ty body''

    , rule "subst-uncurry" $ do
        (tys, ty, a, repl, tys', ty') <- fresh
        prem  $ tySubstList tys a repl tys'
        prem  $ tySubst ty a repl ty'
        concl $ tySubst (tuncurry tys ty) a repl (tuncurry tys' ty')

    , rule "subst-list" $ do
        (ty, a, repl, ty') <- fresh
        prem  $ tySubst ty a repl ty'
        concl $ tySubst (tlist ty) a repl (tlist ty')

    , rule "subst-prod" $ do
        (ty1, ty2, a, repl, ty1', ty2') <- fresh
        prem  $ tySubst ty1 a repl ty1'
        prem  $ tySubst ty2 a repl ty2'
        concl $ tySubst (tprod ty1 ty2) a repl (tprod ty1' ty2')

    , rule "subst-st" $ do
        (ty1, ty2, a, repl, ty1', ty2') <- fresh
        prem  $ tySubst ty1 a repl ty1'
        prem  $ tySubst ty2 a repl ty2'
        concl $ tySubst (tst ty1 ty2) a repl (tst ty1' ty2')
    ]

--------------------------------------------------------------------------------
-- Polarized subtyping (ssub)
--------------------------------------------------------------------------------

ssub :: Judgment "ssub" '[I, I, I, I, I, O] '[Env, Env, Ty, Polar, Ty, Env]
ssub = judgment $
  format (\env senv ty1 p ty2 senv' ->
    env <+> "; " <+> senv <+> " |- " <+> ty1 <+> " " <+> p <+> " " <+> ty2 <+> " |- " <+> senv')
  P.>> rules
    [ rule "S-Int" $ do
        (env, senv, p) <- fresh
        concl $ ssub env senv tint p tint senv

    , rule "S-Bool" $ do
        (env, senv, p) <- fresh
        concl $ ssub env senv tbool p tbool senv

    , rule "S-Refl" $ do
        (env, senv, a, p, envAll) <- fresh
        prem  $ envConcat env senv envAll
        prem  $ lookupUvar envAll a
        concl $ ssub env senv (tvar a) p (tvar a) senv

    , rule "S-MVar-L" $ do
        (env, senv, a, tyA, senv', envAll) <- fresh
        prem  $ envConcat env senv envAll
        prem  $ lookupEvar envAll a
        prem  $ inst senv a tyA senv'
        concl $ ssub env senv (tvar a) pos tyA senv'

    , rule "S-SVar-L" $ do
        (env, senv, a, tyA, tyB, envAll) <- fresh
        prem  $ envConcat env senv envAll
        prem  $ lookupSvar envAll a tyB
        tyA === tyB
        concl $ ssub env senv (tvar a) pos tyA senv

    , rule "S-MVar-R" $ do
        (env, senv, a, tyA, senv', envAll) <- fresh
        prem  $ envConcat env senv envAll
        prem  $ lookupEvar envAll a
        prem  $ inst senv a tyA senv'
        concl $ ssub env senv tyA neg (tvar a) senv'

    , rule "S-SVar-R" $ do
        (env, senv, a, tyA, tyB, envAll) <- fresh
        prem  $ envConcat env senv envAll
        prem  $ lookupSvar envAll a tyB
        tyA === tyB
        concl $ ssub env senv tyA neg (tvar a) senv

    , rule "S-Arr" $ do
        (env, senv, tyA, tyB, tyC, tyD, p, p', senv', senv'') <- fresh
        prem  $ flipPolar p p'
        prem  $ ssub env senv tyC p' tyA senv'
        prem  $ ssub env senv' tyB p tyD senv''
        concl $ ssub env senv (tarr tyA tyB) p (tarr tyC tyD) senv''

    , rule "S-Uncurry" $ do
        (env, senv, tysA, tyA, tysC, tyD, p, senv', senv'') <- fresh
        prem  $ ssubArgs env senv p tysA tysC senv'
        prem  $ ssub env senv' tyA p tyD senv''
        concl $ ssub env senv (tuncurry tysA tyA) p (tuncurry tysC tyD) senv''

    , rule "S-Forall" $ do
        (env, senv, tyA, tyB, p, senv') <- fresh
        a <- freshName
        prem  $ ssub env (euvar a senv) tyA p tyB (euvar a senv')
        concl $ ssub env senv (tforall a tyA) p (tforall a tyB) senv'

    , rule "S-List" $ do
        (env, senv, tyA, tyB, p, senv') <- fresh
        prem  $ ssub env senv tyA p tyB senv'
        concl $ ssub env senv (tlist tyA) p (tlist tyB) senv'

    , rule "S-Prod" $ do
        (env, senv, tyA, tyB, tyC, tyD, p, senv', senv'') <- fresh
        prem  $ ssub env senv tyA p tyC senv'
        prem  $ ssub env senv' tyB p tyD senv''
        concl $ ssub env senv (tprod tyA tyB) p (tprod tyC tyD) senv''

    , rule "S-ST" $ do
        (env, senv, tyA, tyB, tyC, tyD, p, senv', senv'', senv''') <- fresh
        prem  $ ssub env senv tyA p tyC senv'
        prem  $ ssub env senv' tyB p tyD senv''
        prem  $ ssub env senv'' tyC p tyA senv'''
        concl $ ssub env senv (tst tyA tyB) p (tst tyC tyD) senv'''
    ]

ssubArgs :: Judgment "ssubArgs" '[I, I, I, I, I, O] '[Env, Env, Polar, [Ty], [Ty], Env]
ssubArgs = judgment $
  format (\env senv p tysA tysC senv' ->
    env <+> "; " <+> senv <+> " |- " <+> tysA <+> " " <+> p <+> " " <+> tysC <+> " |- " <+> senv')
  P.>> rules
    [ rule "args-nil" $ do
        (env, senv, p) <- fresh
        concl $ ssubArgs env senv p lnil lnil senv

    , rule "args-cons" $ do
        (env, senv, p, p', tyA, tysA, tyC, tysC, senv', senv'') <- fresh
        prem  $ flipPolar p p'
        prem  $ ssub env senv tyC p' tyA senv'
        prem  $ ssubArgs env senv' p tysA tysC senv''
        concl $ ssubArgs env senv p (lcons tyA tysA) (lcons tyC tysC) senv''
    ]

--------------------------------------------------------------------------------
-- Uncurry inference
--------------------------------------------------------------------------------

inferUncurry :: Judgment "inferUncurry" '[I, I, I, I, O, O] '[Env, Env, Ty, Tm, Env, Ty]
inferUncurry = judgment $
  format (\env senv ty tm senv' ty' ->
    env <+> "; " <+> senv <+> " |- " <+> ty <+> " <= " <+> tm <+> " => " <+> senv' <+> ", " <+> ty')
  P.>> rules
    [ rule "UC-Infer" $ do
        (env, senv, tyA, tm, tyA', senv', envAll) <- fresh
        prem  $ envConcat env senv envAll
        prem  $ open envAll tyA
        prem  $ infer envAll cempty tm tyA'
        prem  $ ssub env senv tyA' neg tyA senv'
        concl $ inferUncurry env senv tyA tm senv' tyA'

    , rule "UC-Check" $ do
        (env, senv, tyA, tm, tyA', tyC, envAll) <- fresh
        prem  $ envConcat env senv envAll
        prem  $ closed envAll tyA
        prem  $ ground envAll tyA tyA'
        prem  $ infer envAll (cfulltype tyA') tm tyC
        concl $ inferUncurry env senv tyA tm senv tyA
    ]

--------------------------------------------------------------------------------
-- Algorithmic subtyping (sub)
--------------------------------------------------------------------------------

sub :: Judgment "sub" '[I, I, I, I, O, O] '[Env, Env, Ty, Context, Env, Ty]
sub = judgment $
  format (\env senv ty ctx senv' ty' ->
    env <+> "; " <+> senv <+> " |- " <+> ty <+> " <: " <+> ctx <+> " |- " <+> senv' <+> " => " <+> ty')
  P.>> rules
    [ rule "S-Empty" $ do
        (env, senv, ty, ty', envAll) <- fresh
        prem  $ envConcat env senv envAll
        prem  $ closed envAll ty
        prem  $ ground envAll ty ty'
        concl $ sub env senv ty cempty senv ty'

    , rule "S-Type" $ do
        (env, senv, tyA, tyB, senv') <- fresh
        prem  $ ssub env senv tyA pos tyB senv'
        concl $ sub env senv tyA (cfulltype tyB) senv' tyB

    , rule "S-Term-Closed" $ do
        (env, senv, tyA, tyB, tm, h, tyC, tyD, senv', envAll, tyA') <- fresh
        prem  $ envConcat env senv envAll
        prem  $ closed envAll tyA
        prem  $ ground envAll tyA tyA'
        prem  $ infer envAll (cfulltype tyA') tm tyC
        prem  $ sub env senv tyB h senv' tyD
        concl $ sub env senv (tarr tyA tyB) (cterm tm h) senv' (tarr tyC tyD)

    , rule "S-Term-Open" $ do
        (env, senv, tyA, tyB, tm, h, tyC, tyD, senv', senv'', envAll) <- fresh
        prem  $ envConcat env senv envAll
        prem  $ open envAll tyA
        prem  $ infer envAll cempty tm tyC
        prem  $ ssub env senv tyC neg tyA senv'
        prem  $ sub env senv' tyB h senv'' tyD
        concl $ sub env senv (tarr tyA tyB) (cterm tm h) senv'' (tarr tyC tyD)

    , rule "S-Arr-UC" $ do
        (env, senv, tysA, tyB, tms, h, senv', senv'', tysA', tyB') <- fresh
        prem  $ inferUncurryList env senv tysA tms senv' tysA'
        prem  $ sub env senv' tyB h senv'' tyB'
        concl $ sub env senv (tuncurry tysA tyB) (cuncurry tms h) senv'' (tuncurry tysA' tyB')

    , rule "S-Forall-L" $ do
        (env, senv, tyA, tm, h, senv', tyB, tyC) <- fresh
        a <- freshName
        prem  $ sub env (eevar a senv) tyA (cterm tm h) (esvar a tyB senv') tyC
        concl $ sub env senv (tforall a tyA) (cterm tm h) senv' tyC

    , rule "S-Forall-L-UC" $ do
        (env, senv, tyA, tms, h, senv', tyB, tyC) <- fresh
        a <- freshName
        prem  $ sub env (eevar a senv) tyA (cuncurry tms h) (esvar a tyB senv') tyC
        concl $ sub env senv (tforall a tyA) (cuncurry tms h) senv' tyC

    , rule "S-Svar" $ do
        (env, senv, a, tyA, ctx, senv', tyB, envAll) <- fresh
        prem  $ envConcat env senv envAll
        prem  $ lookupSvar envAll a tyA
        prem  $ sub env senv tyA ctx senv' tyB
        concl $ sub env senv (tvar a) ctx senv' tyB

    , rule "S-Infers" $ do
        (env, senv, a, tm, h, tyA, senv', envAll) <- fresh
        prem  $ envConcat env senv envAll
        prem  $ lookupUvar envAll a
        prem  $ infers envAll (cterm tm h) tyA
        prem  $ inst senv a tyA senv'
        concl $ sub env senv (tvar a) (cterm tm h) senv' tyA

    , rule "S-Prod-Fst" $ do
        (env, senv, tyA, tyB, h, senv', tyA') <- fresh
        prem  $ sub env senv tyA h senv' tyA'
        concl $ sub env senv (tprod tyA tyB) (cfst h) senv' (tprod tyA' tyB)

    , rule "S-Prod-Snd" $ do
        (env, senv, tyA, tyB, h, senv', tyB') <- fresh
        prem  $ sub env senv tyB h senv' tyB'
        concl $ sub env senv (tprod tyA tyB) (csnd h) senv' (tprod tyA tyB')
    ]

--------------------------------------------------------------------------------
-- Context inference (infers)
--------------------------------------------------------------------------------

infers :: Judgment "infers" '[I, I, O] '[Env, Context, Ty]
infers = judgment $
  format (\env ctx ty -> env <+> " |- " <+> ctx <+> " => " <+> ty)
  P.>> rules
    [ rule "CI-Type" $ do
        (env, ty) <- fresh
        concl $ infers env (cfulltype ty) ty

    , rule "CI-Term" $ do
        (env, tm, h, tyA, tyB) <- fresh
        prem  $ infer env cempty tm tyA
        prem  $ infers env h tyB
        concl $ infers env (cterm tm h) (tarr tyA tyB)
    ]

--------------------------------------------------------------------------------
-- Type inference (infer)
--------------------------------------------------------------------------------

infer :: Judgment "infer" '[I, I, I, O] '[Env, Context, Tm, Ty]
infer = judgment $
  format (\env ctx tm ty -> env <+> " |- " <+> ctx <+> " => " <+> tm <+> " => " <+> ty)
  P.>> rules
    [ rule "Ty-Int" $ do
        (env, n) <- fresh
        concl $ infer env cempty (litInt n) tint

    , rule "Ty-Bool" $ do
        (env, b) <- fresh
        concl $ infer env cempty (litBool b) tbool

    , rule "Ty-Var" $ do
        (env, x, ty) <- fresh
        prem  $ lookupTmVar env x ty
        concl $ infer env cempty (var x) ty

    , rule "Ty-Ann" $ do
        (env, tm, ty, ty') <- fresh
        prem  $ infer env (cfulltype ty) tm ty'
        concl $ infer env cempty (ann tm ty) ty

    , rule "Ty-App" $ do
        (env, ctx, tm1, tm2, tyA, tyB) <- fresh
        prem  $ infer env (cterm tm2 ctx) tm1 (tarr tyA tyB)
        concl $ infer env ctx (app tm1 tm2) tyB

    , rule "Ty-App-UC" $ do
        (env, ctx, tm1, tms, tys, tyB) <- fresh
        prem  $ infer env (cuncurry tms ctx) tm1 (tuncurry tys tyB)
        concl $ infer env ctx (appUncurry tm1 tms) tyB

    , rule "Ty-Abs1" $ do
        (env, x, body, tyA, tyB, tyC) <- fresh
        prem  $ infer (etrm x tyA env) (cfulltype tyB) body tyC
        concl $ infer env (cfulltype (tarr tyA tyB)) (abs x body) (tarr tyA tyC)

    , rule "Ty-Abs2" $ do
        (env, x, body, tm2, h, tyA, tyB) <- fresh
        prem  $ infer env cempty tm2 tyA
        prem  $ infer (etrm x tyA env) h body tyB
        concl $ infer env (cterm tm2 h) (abs x body) (tarr tyA tyB)

    , rule "Ty-AbsAnn1" $ do
        (env, x, tyA, tyA', tyB, body, tyC) <- fresh
        tyA === tyA'
        prem  $ infer (etrm x tyA env) (cfulltype tyB) body tyC
        concl $ infer env (cfulltype (tarr tyA tyB)) (absAnn (tup x tyA') body) (tarr tyA tyB)

    , rule "Ty-AbsAnn2" $ do
        (env, x, tyA, tm2, h, body, tyB, tyC) <- fresh
        prem  $ infer env (cfulltype tyA) tm2 tyC
        prem  $ infer (etrm x tyA env) h body tyB
        concl $ infer env (cterm tm2 h) (absAnn (tup x tyA) body) (tarr tyA tyB)

    , rule "Ty-AbsAnn3" $ do
        (env, x, tyA, body, tyB) <- fresh
        prem  $ infer (etrm x tyA env) cempty body tyB
        concl $ infer env cempty (absAnn (tup x tyA) body) (tarr tyA tyB)

    , rule "Ty-AbsAnn-UC1" $ do
        (env, anns, xs, tysAnn, tysCtx, tyB, body, env', tyC) <- fresh
        prem  $ splitAnnList anns xs tysAnn
        prem  $ tyZipEq tysCtx tysAnn
        prem  $ extendEnvZip xs tysAnn env env'
        prem  $ infer env' (cfulltype tyB) body tyC
        concl $ infer env (cfulltype (tuncurry tysCtx tyB)) (absUncurryAnn anns body) (tuncurry tysCtx tyB)

    , rule "Ty-AbsAnn-UC2" $ do
        (env, anns, xs, tys, tms, h, body, env', tyB) <- fresh
        prem  $ splitAnnList anns xs tys
        prem  $ inferZip env tys tms
        prem  $ extendEnvZip xs tys env env'
        prem  $ infer env' h body tyB
        concl $ infer env (cuncurry tms h) (absUncurryAnn anns body) (tuncurry tys tyB)

    , rule "Ty-AbsAnn-UC3" $ do
        (env, anns, xs, tys, body, env', tyB) <- fresh
        prem  $ splitAnnList anns xs tys
        prem  $ extendEnvZip xs tys env env'
        prem  $ infer env' cempty body tyB
        concl $ infer env cempty (absUncurryAnn anns body) (tuncurry tys tyB)

    , rule "Ty-Abs-UC1" $ do
        (env, xs, tys, tyB, body, env', tyC) <- fresh
        prem  $ extendEnvZip xs tys env env'
        prem  $ infer env' (cfulltype tyB) body tyC
        concl $ infer env (cfulltype (tuncurry tys tyB)) (absUncurry xs body) (tuncurry tys tyC)

    , rule "Ty-Abs-UC2" $ do
        (env, xs, tms, h, body, tys, env', tyB) <- fresh
        prem  $ inferList env tms tys
        prem  $ extendEnvZip xs tys env env'
        prem  $ infer env' h body tyB
        concl $ infer env (cuncurry tms h) (absUncurry xs body) (tuncurry tys tyB)

    , rule "Ty-TAbs" $ do
        (env, a, body, tyA) <- fresh
        prem  $ infer (euvar a env) cempty body tyA
        concl $ infer env cempty (tabs a body) (tforall a tyA)

    , rule "Ty-TAbs-Chk" $ do
        (env, a, tyA, body, tyB) <- fresh
        prem  $ infer (euvar a env) (cfulltype tyA) body tyB
        concl $ infer env (cfulltype (tforall a tyA)) (tabs a body) (tforall a tyA)

    , rule "Ty-TApp" $ do
        (env, ctx, tm, tyA, a, tyB, tyB', tyC) <- fresh
        prem  $ infer env cempty tm (tforall a tyB)
        prem  $ tySubst tyB a tyA tyB'
        prem  $ sub env eempty tyB' ctx eempty tyC
        concl $ infer env ctx (tapp tm tyA) tyC

    , rule "Ty-Pair1" $ do
        (env, tm1, tm2, tyA, tyB) <- fresh
        prem  $ infer env cempty tm1 tyA
        prem  $ infer env cempty tm2 tyB
        concl $ infer env cempty (pair tm1 tm2) (tprod tyA tyB)

    , rule "Ty-Pair2" $ do
        (env, tm1, tm2, tyA, tyB, tyA', tyB') <- fresh
        prem  $ infer env (cfulltype tyA) tm1 tyA'
        prem  $ infer env (cfulltype tyB) tm2 tyB'
        concl $ infer env (cfulltype (tprod tyA tyB)) (pair tm1 tm2) (tprod tyA' tyB')

    , rule "Ty-Fst" $ do
        (env, ctx, tm, tyA, tyB) <- fresh
        prem  $ infer env (cfst ctx) tm (tprod tyA tyB)
        concl $ infer env ctx (fst tm) tyA

    , rule "Ty-Snd" $ do
        (env, ctx, tm, tyA, tyB) <- fresh
        prem  $ infer env (csnd ctx) tm (tprod tyA tyB)
        concl $ infer env ctx (snd tm) tyB

    , rule "Ty-Pair-Fst" $ do
        (env, tm1, tm2, h, tyA, tyB) <- fresh
        prem  $ infer env h tm1 tyA
        prem  $ infer env cempty tm2 tyB
        concl $ infer env (cfst h) (pair tm1 tm2) (tprod tyA tyB)

    , rule "Ty-Pair-Snd" $ do
        (env, tm1, tm2, h, tyA, tyB) <- fresh
        prem  $ infer env cempty tm1 tyA
        prem  $ infer env h tm2 tyB
        concl $ infer env (csnd h) (pair tm1 tm2) (tprod tyA tyB)

    , rule "Ty-Sub" $ do
        (env, ctx, tm, tyA, tyB) <- fresh
        prem  $ genericConsumer tm
        prem  $ nonEmptyContext ctx
        prem  $ infer env cempty tm tyA
        prem  $ sub env eempty tyA ctx eempty tyB
        concl $ infer env ctx tm tyB

    , rule "Ty-Nil-Chk" $ do
        (env, ty) <- fresh
        concl $ infer env (cfulltype (tlist ty)) nil (tlist ty)

    , rule "Ty-Nil" $ do
        env <- fresh
        a <- freshName
        concl $ infer env cempty nil (tforall a (tlist (tvar a)))
    ]
