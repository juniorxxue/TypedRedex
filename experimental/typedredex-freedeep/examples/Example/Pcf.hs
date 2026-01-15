{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE TypeFamilies #-}

module Example.Pcf
  ( Tm(..)
  , zero
  , succTm
  , predTm
  , if0
  , plus
  , add
  , evalP
  , one
  , two
  , three
  ) where

import TypedRedex.DSL
import qualified TypedRedex.DSL as R

--------------------------------------------------------------------------------
-- Syntax
--------------------------------------------------------------------------------

data Tm
  = Zero
  | Succ Tm
  | Pred Tm
  | If0 Tm Tm Tm
  | Plus Tm Tm
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Repr instance
--------------------------------------------------------------------------------

instance Repr Tm where
  data Reified Tm
    = RZero
    | RSucc (Logic Tm)
    | RPred (Logic Tm)
    | RIf0 (Logic Tm) (Logic Tm) (Logic Tm)
    | RPlus (Logic Tm) (Logic Tm)

  project Zero = RZero
  project (Succ t) = RSucc (Ground (project t))
  project (Pred t) = RPred (Ground (project t))
  project (If0 t1 t2 t3) = RIf0 (Ground (project t1)) (Ground (project t2)) (Ground (project t3))
  project (Plus t1 t2) = RPlus (Ground (project t1)) (Ground (project t2))

  reify RZero = Just Zero
  reify (RSucc (Ground t)) = Succ <$> reify t
  reify (RPred (Ground t)) = Pred <$> reify t
  reify (RIf0 (Ground t1) (Ground t2) (Ground t3)) = If0 <$> reify t1 <*> reify t2 <*> reify t3
  reify (RPlus (Ground t1) (Ground t2)) = Plus <$> reify t1 <*> reify t2
  reify _ = Nothing

  quote RZero = ("Zero", [])
  quote (RSucc t) = ("Succ", [Field t])
  quote (RPred t) = ("Pred", [Field t])
  quote (RIf0 t1 t2 t3) = ("If0", [Field t1, Field t2, Field t3])
  quote (RPlus t1 t2) = ("Plus", [Field t1, Field t2])

  mapReified _ RZero = RZero
  mapReified f (RSucc t) = RSucc (f t)
  mapReified f (RPred t) = RPred (f t)
  mapReified f (RIf0 t1 t2 t3) = RIf0 (f t1) (f t2) (f t3)
  mapReified f (RPlus t1 t2) = RPlus (f t1) (f t2)

--------------------------------------------------------------------------------
-- Smart constructors
--------------------------------------------------------------------------------

zero :: Term Tm
zero = ground Zero

succTm :: Term Tm -> Term Tm
succTm = lift1 (\t -> Ground (RSucc t))

predTm :: Term Tm -> Term Tm
predTm = lift1 (\t -> Ground (RPred t))

if0 :: Term Tm -> Term Tm -> Term Tm -> Term Tm
if0 = lift3 (\t1 t2 t3 -> Ground (RIf0 t1 t2 t3))

plus :: Term Tm -> Term Tm -> Term Tm
plus = lift2 (\t1 t2 -> Ground (RPlus t1 t2))

one :: Term Tm
one = succTm zero

two :: Term Tm
two = succTm one

three :: Term Tm
three = succTm two

--------------------------------------------------------------------------------
-- Judgments
--------------------------------------------------------------------------------

add :: Judgment "add" '[I, I, O] '[Tm, Tm, Tm]
add = judgment
  [ rule "add-zero" $ R.do
      y <- R.fresh
      R.concl $ add # (zero, y, y)

  , rule "add-succ" $ R.do
      x <- R.fresh
      y <- R.fresh
      z <- R.fresh
      R.concl $ add # (succTm x, y, succTm z)
      R.prem  $ add # (x, y, z)
  ]

evalP :: Judgment "eval" '[I, O] '[Tm, Tm]
evalP = judgment
  [ rule "eval-zero" $ R.do
      R.concl $ evalP # (zero, zero)

  , rule "eval-succ" $ R.do
      t <- R.fresh
      v <- R.fresh
      R.concl $ evalP # (succTm t, succTm v)
      R.prem  $ evalP # (t, v)

  , rule "eval-pred-zero" $ R.do
      R.concl $ evalP # (predTm zero, zero)

  , rule "eval-pred-succ" $ R.do
      t <- R.fresh
      v <- R.fresh
      R.concl $ evalP # (predTm (succTm t), v)
      R.prem  $ evalP # (t, v)

  , rule "eval-if0-zero" $ R.do
      t <- R.fresh
      t1 <- R.fresh
      t2 <- R.fresh
      v <- R.fresh
      R.concl $ evalP # (if0 t t1 t2, v)
      R.prem  $ evalP # (t, zero)
      R.prem  $ evalP # (t1, v)

  , rule "eval-if0-succ" $ R.do
      t <- R.fresh
      n <- R.fresh
      t1 <- R.fresh
      t2 <- R.fresh
      v <- R.fresh
      R.concl $ evalP # (if0 t t1 t2, v)
      R.prem  $ evalP # (t, succTm n)
      R.prem  $ evalP # (t2, v)

  , rule "eval-plus" $ R.do
      t1 <- R.fresh
      t2 <- R.fresh
      v1 <- R.fresh
      v2 <- R.fresh
      v <- R.fresh
      R.concl $ evalP # (plus t1 t2, v)
      R.prem  $ evalP # (t1, v1)
      R.prem  $ evalP # (t2, v2)
      R.prem  $ add # (v1, v2, v)
  ]
