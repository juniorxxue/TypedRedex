{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RebindableSyntax #-}

-- | Auxiliary judgments for Signal type system.
module Signal.Rules
  ( flipPolar
  , envConcat
  , lookupTmVar
  , lookupUvar
  , lookupEvar
  , lookupSvar
  , inst
  ) where

import Data.String (fromString)
import Prelude hiding ((>>=), (>>), return)
import qualified Prelude as P
import TypedRedex.DSL hiding (neg, var)
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
        a =/= b
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

--------------------------------------------------------------------------------
-- Instantiation (solve an existential variable)
--------------------------------------------------------------------------------

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
