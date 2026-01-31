{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RebindableSyntax #-}

module STLC.Rules
  ( addNat
  , lookupVar
  , typeof
  , value
  , subst
  , step
  ) where

import Data.String (fromString)
import Prelude hiding ((>>=), (>>), return)
import qualified Prelude as P
import TypedRedex.DSL hiding (var)
import TypedRedex.Nominal.Prelude (Nom)
import TypedRedex.Pretty ((<+>))
import Support.Nat (Nat, zro, suc)

import STLC.Syntax

--------------------------------------------------------------------------------
-- Natural-number addition (δ+)
--------------------------------------------------------------------------------

-- | Relational addition on naturals.
addNat :: Judgment "add" '[I, I, O] '[Nat, Nat, Nat]
addNat = judgment $
  format (\x y z -> x <+> " + " <+> y <+> " = " <+> z)
  P.>> rules
    [ rule "add-zero" $ do
        y <- fresh
        concl $ addNat zro y y

    , rule "add-succ" $ do
        (x, y, z) <- fresh
        prem  $ addNat x y z
        concl $ addNat (suc x) y (suc z)
    ]

--------------------------------------------------------------------------------
-- Environments
--------------------------------------------------------------------------------

-- | Γ(x) = A
lookupVar :: Judgment "lookup" '[I, I, O] '[Env, Nom, Ty]
lookupVar = judgment $
  format (\env x ty -> env <+> " (" <+> x <+> ") = " <+> ty)
  P.>> rules
    [ rule "here" $ do
        (env, x, ty) <- fresh
        concl $ lookupVar (ebind x ty env) x ty

    , rule "skip" $ do
        (env, x, y, ty, ty') <- fresh
        x =/= y
        prem  $ lookupVar env x ty
        concl $ lookupVar (ebind y ty' env) x ty
    ]

--------------------------------------------------------------------------------
-- Typing
--------------------------------------------------------------------------------

typeof :: Judgment "typeof" '[I, I, O] '[Env, Tm, Ty]
typeof = judgment $
  format (\env tm ty -> env <+> " ⊢ " <+> tm <+> " : " <+> ty)
  P.>> rules
    [ rule "T-Var" $ do
        (env, x, ty) <- fresh
        prem  $ lookupVar env x ty
        concl $ typeof env (var x) ty

    , rule "T-Abs" $ do
        (env, x, tyA, body, tyB) <- fresh
        prem  $ typeof (ebind x tyA env) body tyB
        concl $ typeof env (lam tyA x body) (tarr tyA tyB)

    , rule "T-App" $ do
        (env, t1, t2, tyA, tyB) <- fresh
        prem  $ typeof env t1 (tarr tyA tyB)
        prem  $ typeof env t2 tyA
        concl $ typeof env (app t1 t2) tyB

    , rule "T-Lit" $ do
        (env, n) <- fresh
        concl $ typeof env (lit n) tint

    , rule "T-Add" $ do
        (env, t1, t2) <- fresh
        prem  $ typeof env t1 tint
        prem  $ typeof env t2 tint
        concl $ typeof env (plus t1 t2) tint

    , rule "T-True" $ do
        env <- fresh
        concl $ typeof env true tbool

    , rule "T-False" $ do
        env <- fresh
        concl $ typeof env false tbool

    , rule "T-If" $ do
        (env, c, t, e, ty) <- fresh
        prem  $ typeof env c tbool
        prem  $ typeof env t ty
        prem  $ typeof env e ty
        concl $ typeof env (ifte c t e) ty
    ]

--------------------------------------------------------------------------------
-- Values
--------------------------------------------------------------------------------

value :: Judgment "value" '[I] '[Tm]
value = judgment $
  format (\tm -> "value " <+> tm)
  P.>> rules
    [ rule "V-Lit" $ do
        n <- fresh
        concl $ value (lit n)

    , rule "V-True" $ do
        concl $ value true

    , rule "V-False" $ do
        concl $ value false

    , rule "V-Lam" $ do
        (ty, body) <- fresh
        x <- freshName
        concl $ value (lam ty x body)
    ]

--------------------------------------------------------------------------------
-- Substitution (e[v/x])
--------------------------------------------------------------------------------

subst :: Judgment "subst" '[I, I, I, O] '[Tm, Nom, Tm, Tm]
subst = judgment $
  format (\body x repl res -> "[" <+> repl <+> "/" <+> x <+> "] " <+> body <+> " = " <+> res)
  P.>> rules
    [ rule "subst-var-hit" $ do
        (x, repl) <- fresh
        concl $ subst (var x) x repl repl

    , rule "subst-var-miss" $ do
        (x, y, repl) <- fresh
        x =/= y
        concl $ subst (var y) x repl (var y)

    , rule "subst-lit" $ do
        (n, x, repl) <- fresh
        concl $ subst (lit n) x repl (lit n)

    , rule "subst-true" $ do
        (x, repl) <- fresh
        concl $ subst true x repl true

    , rule "subst-false" $ do
        (x, repl) <- fresh
        concl $ subst false x repl false

    , rule "subst-lam" $ do
        (ty, x, repl, body, body') <- fresh
        y <- freshName
        -- Ensure binder does not capture free occurrences in the replacement.
        hash y repl
        prem  $ subst body x repl body'
        concl $ subst (lam ty y body) x repl (lam ty y body')

    , rule "subst-app" $ do
        (t1, t2, x, repl, t1', t2') <- fresh
        prem  $ subst t1 x repl t1'
        prem  $ subst t2 x repl t2'
        concl $ subst (app t1 t2) x repl (app t1' t2')

    , rule "subst-plus" $ do
        (t1, t2, x, repl, t1', t2') <- fresh
        prem  $ subst t1 x repl t1'
        prem  $ subst t2 x repl t2'
        concl $ subst (plus t1 t2) x repl (plus t1' t2')

    , rule "subst-if" $ do
        (c, t, e, x, repl, c', t', e') <- fresh
        prem  $ subst c x repl c'
        prem  $ subst t x repl t'
        prem  $ subst e x repl e'
        concl $ subst (ifte c t e) x repl (ifte c' t' e')
    ]

--------------------------------------------------------------------------------
-- Small-step evaluation (e --> e')
--------------------------------------------------------------------------------

step :: Judgment "step" '[I, O] '[Tm, Tm]
step = judgment $
  format (\t t' -> t <+> " --> " <+> t')
  P.>> rules
    [ rule "β" $ do
        (ty, body, v, body') <- fresh
        x <- freshName
        prem  $ value v
        prem  $ subst body x v body'
        concl $ step (app (lam ty x body) v) body'

    , rule "δ+" $ do
        (n1, n2, n3) <- fresh
        prem  $ addNat n1 n2 n3
        concl $ step (plus (lit n1) (lit n2)) (lit n3)

    , rule "ifT" $ do
        (t, e) <- fresh
        concl $ step (ifte true t e) t

    , rule "ifF" $ do
        (t, e) <- fresh
        concl $ step (ifte false t e) e

    , rule "app1" $ do
        (t1, t1', t2) <- fresh
        prem  $ step t1 t1'
        concl $ step (app t1 t2) (app t1' t2)

    , rule "app2" $ do
        (v1, t2, t2') <- fresh
        prem  $ value v1
        prem  $ step t2 t2'
        concl $ step (app v1 t2) (app v1 t2')

    , rule "+1" $ do
        (t1, t1', t2) <- fresh
        prem  $ step t1 t1'
        concl $ step (plus t1 t2) (plus t1' t2)

    , rule "+2" $ do
        (n1, t2, t2') <- fresh
        prem  $ step t2 t2'
        concl $ step (plus (lit n1) t2) (plus (lit n1) t2')

    , rule "ifC" $ do
        (c, c', t, e) <- fresh
        prem  $ step c c'
        concl $ step (ifte c t e) (ifte c' t e)
    ]

