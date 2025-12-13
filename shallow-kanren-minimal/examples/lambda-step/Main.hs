{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Main (main) where

import Control.Applicative (empty)
import Shallow.Core.Kanren
import Shallow.Core.Internal.Logic (Logic (Ground), LogicType (..))
import Shallow.Interpreters.SubstKanren (runSubstKanren, takeS, Stream)
import Shallow.Utils.Type (quote0, quote1, quote2)

-- A tiny Peano type for de Bruijn indices.
data Nat = Z | S Nat deriving (Eq, Show)

instance LogicType Nat where
  data Reified Nat var = ZR | SR (Logic Nat var)

  project Z = ZR
  project (S n) = SR (Ground $ project n)

  reify ZR = Just Z
  reify (SR (Ground n)) = S <$> reify n
  reify _ = Nothing

  quote ZR = quote0 "Z" ZR
  quote (SR n) = quote1 "S" SR n

  unifyVal _ ZR ZR = pure ()
  unifyVal unif (SR x) (SR y) = unif x y
  unifyVal _ _ _ = empty

  derefVal _ ZR = pure Z
  derefVal deref (SR n) = S <$> deref n

zro :: Logic Nat var
zro = Ground ZR

suc :: Logic Nat var -> Logic Nat var
suc = Ground . SR

-- Lambda-terms (de Bruijn).
data Tm = Var Nat | Lam Tm | App Tm Tm deriving (Eq, Show)

instance LogicType Tm where
  data Reified Tm var
    = VarR (Logic Nat var)
    | LamR (Logic Tm var)
    | AppR (Logic Tm var) (Logic Tm var)

  project (Var n) = VarR (Ground $ project n)
  project (Lam b) = LamR (Ground $ project b)
  project (App f a) = AppR (Ground $ project f) (Ground $ project a)

  reify (VarR (Ground n)) = Var <$> reify n
  reify (LamR (Ground b)) = Lam <$> reify b
  reify (AppR (Ground f) (Ground a)) = App <$> reify f <*> reify a
  reify _ = Nothing

  quote (VarR n) = quote1 "Var" VarR n
  quote (LamR b) = quote1 "Lam" LamR b
  quote (AppR f a) = quote2 "App" AppR f a

  unifyVal unif (VarR n) (VarR n') = unif n n'
  unifyVal unif (LamR b) (LamR b') = unif b b'
  unifyVal unif (AppR f a) (AppR f' a') = unif f f' *> unif a a'
  unifyVal _ _ _ = empty

  derefVal deref (VarR n) = Var <$> deref n
  derefVal deref (LamR b) = Lam <$> deref b
  derefVal deref (AppR f a) = App <$> deref f <*> deref a

var :: Logic Nat var -> Logic Tm var
var = Ground . VarR

lam :: Logic Tm var -> Logic Tm var
lam = Ground . LamR

app :: Logic Tm var -> Logic Tm var -> Logic Tm var
app f a = Ground $ AppR f a

-- A minimal call-by-value value predicate: only lambdas are values.
value :: (Kanren rel) => L Tm rel -> Relation rel
value = relation "value" $ \t -> fresh $ \b -> t <=> lam b

-- Naive β-substitution for de Bruijn index 0:
--   subst0 body arg out  means  out = body[arg/0]
--
-- This is intentionally small (not capture-avoiding under λ).
subst0 :: (Kanren rel) => L Tm rel -> L Tm rel -> L Tm rel -> Relation rel
subst0 = relation3 "subst0" $ \body arg out ->
  conde
    [ -- Do not substitute under binders (toy example).
      fresh $ \b -> do
        body <=> lam b
        out <=> lam b
        pure ()
    , -- Variables: 0 ↦ arg, (S n) ↦ (Var n)
      fresh2 $ \n n' -> do
        body <=> var n
        conde
          [ do
              n <=> zro
              out <=> arg
              pure ()
          , do
              n <=> suc n'
              out <=> var n'
              pure ()
          ]
        pure ()
    , -- Applications: recurse.
      fresh4 $ \f a f' a' -> do
        body <=> app f a
        call $ subst0 f arg f'
        call $ subst0 a arg a'
        out <=> app f' a'
        pure ()
    ]

-- Rule composition helper (avoids repeating t/t').
alts2 :: (Kanren rel) => [L a rel -> L b rel -> Relation rel] -> L a rel -> L b rel -> rel ()
alts2 rules x y = conde [call (r x y) | r <- rules]

-- Single-step semantics, split into separate rules and composed.
stepBeta :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
stepBeta = relation2 "step_beta" $ \t t' -> fresh2 $ \b v -> do
  t <=> app (lam b) v
  call $ value v
  call $ subst0 b v t'
  pure ()

stepAppL :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
stepAppL = relation2 "step_appL" $ \t t' -> fresh3 $ \t1 t1' t2 -> do
  t <=> app t1 t2
  t' <=> app t1' t2
  call $ step t1 t1'
  pure ()

stepAppR :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
stepAppR = relation2 "step_appR" $ \t t' -> fresh3 $ \v t2 t2' -> do
  call $ value v
  t <=> app v t2
  t' <=> app v t2'
  call $ step t2 t2'
  pure ()

step :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
step = relation2 "step" (alts2 [stepBeta, stepAppL, stepAppR])

-- Run step in mode (I,O): given a ground term, enumerate its one-step results.
stepIO :: Tm -> Stream Tm
stepIO t0 = runSubstKanren $ fresh $ \t' -> do
  _ <- embed $ step (Ground $ project t0) t'
  eval t'

main :: IO ()
main = do
  let id0 = Lam (Var Z)
  let term = App id0 id0
  print $ takeS 5 (stepIO term)
