{-# LANGUAGE TypeFamilies #-}

module Pcf.Syntax
  ( Tm(..)
  , zero
  , succTm
  , predTm
  , if0
  , plus
  , one
  , two
  , three
  ) where

import TypedRedex.Core.Term

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
