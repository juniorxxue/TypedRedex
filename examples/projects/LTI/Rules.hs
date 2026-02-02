{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RebindableSyntax #-}

module LTI.Rules
  ( sub
  , subList
  ) where

import Data.String (fromString)
import Prelude hiding ((>>=), (>>), return)
import qualified Prelude as P
import TypedRedex.DSL
import TypedRedex.Pretty ((<+>))

import LTI.Syntax

{-
[A] <: [B] means S_i <: T_i for all i, and they have the same length.

----------- s-refl
a <: a

----------- s-top
A <: top


----------- s-bot
bot <: A


[C] <: [A]         B <: D
------------------------------------------------ s-arr
forall [a]. [A] -> B <: forall [a]. [C] -> D
-}

--------------------------------------------------------------------------------
-- Subtyping
--------------------------------------------------------------------------------

sub :: Judgment "sub" '[I, I] '[Ty, Ty]
sub = judgment $
  format (\a b -> a <+> " <: " <+> b)
  P.>> rules
    [ rule "s-refl" $ do
        a <- fresh
        concl $ sub (tvar a) (tvar a)

    , rule "s-top" $ do
        a <- fresh
        concl $ sub a ttop

    , rule "s-bot" $ do
        a <- fresh
        concl $ sub tbot a

    , rule "s-arr" $ do
        (as, argsA, argsC, resB, resD) <- fresh
        prem $ subList argsC argsA
        prem $ sub resB resD
        concl $ sub (tforall as argsA resB) (tforall as argsC resD)
    ]

subList :: Judgment "subList" '[I, I] '[ [Ty], [Ty] ]
subList = judgment $
  format (\xs ys -> xs <+> " <: " <+> ys)
  P.>> rules
    [ rule "sub-nil" $ do
        concl $ subList lnil lnil

    , rule "sub-cons" $ do
        (x, xs, y, ys) <- fresh
        prem $ sub x y
        prem $ subList xs ys
        concl $ subList (lcons x xs) (lcons y ys)
    ]

{-
least upper bound

A \/ B ~> C


B <: A
--------------------- lub-l
A \/ B ~> A

A <: B
--------------------- lub-r
A \/ B ~> B


[A] /\ [B] ~> [E]
C \/ D ~> F
----------------------------------------------------------------- lub-arr
forall [a]. [A] -> B \/ forall [a]. [C] -> D ~> forall [a]. [E] -> F



-}