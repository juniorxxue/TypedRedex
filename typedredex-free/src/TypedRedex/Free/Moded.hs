{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QualifiedDo #-}

-- | Mode-Checked DSL using Indexed Free Monad
--
-- This module provides the user-facing API for defining mode-checked
-- logic programming rules using do-notation.
--
-- = Usage
--
-- @
-- {-# LANGUAGE QualifiedDo, DataKinds, TypeApplications #-}
-- import qualified TypedRedex.Free.Moded as R
--
-- lookupCtx :: Judgment3 rel "lookup" '[I, I, O] Ctx Nat Ty
-- lookupCtx = defJudge3 @"lookup" $ \\rule ->
--   [ rule "lookup-here" $ R.do
--       (ty, rest) <- R.fresh2
--       R.concl $ lookupCtx (cons ty rest) zro ty
--
--   , rule "lookup-there" $ R.do
--       (ty', rest, n', ty) <- R.fresh4
--       R.concl $ lookupCtx (cons ty' rest) (suc n') ty
--       R.prem  $ lookupCtx rest n' ty
--   ]
-- @
module TypedRedex.Free.Moded
  ( -- * Rule Monad
    RuleM
  , ModedRule(..)
  , ruleM
    -- * Smart Constructors
  , fresh, fresh2, fresh3, fresh4, fresh5, fresh6
  , concl
  , prem
  , neg
  , (===), (=/=)
  , liftRel
  , liftRelDeferred
    -- * Moded Terms
  , T(..)
  , ground
  , lift1, lift2, lift3
    -- * Argument Lists
  , TArgs(..)
  , ToLTermList(..)
  , LTermList(..)
    -- * Applied Judgments
  , AppliedM(..)
  , toApplied
    -- * Judgment Types
  , Judgment1, Judgment2, Judgment3, Judgment4, Judgment5, Judgment6
    -- * Moded Type Wrappers
  , In, Out, GetMode, GetType
  , MJudgment1, MJudgment2, MJudgment3, MJudgment4, MJudgment5, MJudgment6
    -- * Judgment Definition Helpers
  , mjudge1, mjudge2, mjudge3, mjudge4, mjudge5, mjudge6
  , defJudge1, defJudge2, defJudge3, defJudge4, defJudge5, defJudge6
    -- * Mode Types
  , Mode(..), ModeList(..), SingModeList(..)
    -- * Schedule Checking
  , CheckSchedule
  , Union
    -- * QualifiedDo Support
  , return, (>>=), (>>)
  ) where

import Prelude hiding (return, (>>=), (>>))
import qualified Prelude
import Data.Kind (Type, Constraint)
import Data.Proxy (Proxy(..))
import Data.Set (Set)
import qualified Data.Set as S
import Data.Typeable (Typeable)
import GHC.TypeLits (Symbol, KnownSymbol, symbolVal, Nat, type (+))
import Control.Applicative (asum)

import TypedRedex.Logic
  ( LogicType, Logic(..), Redex(..), RedexNeg, RVar
  , FreshType(..), Relation(..), CapturedTerm(..), CallType(..)
  )
import qualified TypedRedex.Logic as R (neg)
import TypedRedex.Free.IxFree (IxFree(..), liftF)
import qualified TypedRedex.Free.IxFree as Ix
import TypedRedex.Free.RuleF
import TypedRedex.Free.Schedule

--------------------------------------------------------------------------------
-- Rule Monad Type
--------------------------------------------------------------------------------

-- | The Rule Monad: IxFree over RuleF
--
-- @
-- RuleM rel ts s t a
--   rel : the interpreter monad
--   ts  : types of the enclosing judgment
--   s   : input state ('St n steps c)
--   t   : output state
--   a   : result type
-- @
type RuleM rel ts s t a = IxFree (RuleF rel ts) s t a

--------------------------------------------------------------------------------
-- QualifiedDo Support
--------------------------------------------------------------------------------

return :: a -> RuleM rel ts s s a
return = Ix.return

(>>=) :: RuleM rel ts s t a -> (a -> RuleM rel ts t u b) -> RuleM rel ts s u b
(>>=) = (Ix.>>=)

(>>) :: RuleM rel ts s t a -> RuleM rel ts t u b -> RuleM rel ts s u b
(>>) = (Ix.>>)

--------------------------------------------------------------------------------
-- Smart Constructors
--------------------------------------------------------------------------------

-- | Allocate a fresh logic variable
fresh :: forall a rel ts n steps c.
         (LogicType a, Typeable a)
      => RuleM rel ts ('St n steps c) ('St (n + 1) steps c) (T '[n] a rel)
fresh = liftF FreshF

-- | Allocate 2 fresh logic variables
fresh2 :: forall a b rel ts n steps c.
          (LogicType a, Typeable a, LogicType b, Typeable b)
       => RuleM rel ts ('St n steps c) ('St ((n + 1) + 1) steps c)
            (T '[n] a rel, T '[n + 1] b rel)
fresh2 = Ix.do
  a <- fresh @a
  b <- fresh @b
  return (a, b)

-- | Allocate 3 fresh logic variables
fresh3 :: forall a b c rel ts n steps cc.
          (LogicType a, Typeable a, LogicType b, Typeable b, LogicType c, Typeable c)
       => RuleM rel ts ('St n steps cc) ('St (((n + 1) + 1) + 1) steps cc)
            (T '[n] a rel, T '[n + 1] b rel, T '[(n + 1) + 1] c rel)
fresh3 = Ix.do
  a <- fresh @a
  b <- fresh @b
  c <- fresh @c
  return (a, b, c)

-- | Allocate 4 fresh logic variables
fresh4 :: forall a b c d rel ts n steps cc.
          (LogicType a, Typeable a, LogicType b, Typeable b,
           LogicType c, Typeable c, LogicType d, Typeable d)
       => RuleM rel ts ('St n steps cc) ('St ((((n + 1) + 1) + 1) + 1) steps cc)
            (T '[n] a rel, T '[n + 1] b rel, T '[(n + 1) + 1] c rel, T '[((n + 1) + 1) + 1] d rel)
fresh4 = Ix.do
  a <- fresh @a
  b <- fresh @b
  c <- fresh @c
  d <- fresh @d
  return (a, b, c, d)

-- | Allocate 5 fresh logic variables
fresh5 :: forall a b c d e rel ts n steps cc.
          (LogicType a, Typeable a, LogicType b, Typeable b,
           LogicType c, Typeable c, LogicType d, Typeable d,
           LogicType e, Typeable e)
       => RuleM rel ts ('St n steps cc) ('St (((((n + 1) + 1) + 1) + 1) + 1) steps cc)
            (T '[n] a rel, T '[n + 1] b rel, T '[(n + 1) + 1] c rel,
             T '[((n + 1) + 1) + 1] d rel, T '[(((n + 1) + 1) + 1) + 1] e rel)
fresh5 = Ix.do
  a <- fresh @a
  b <- fresh @b
  c <- fresh @c
  d <- fresh @d
  e <- fresh @e
  return (a, b, c, d, e)

-- | Allocate 6 fresh logic variables
fresh6 :: forall a b c d e f rel ts n steps cc.
          (LogicType a, Typeable a, LogicType b, Typeable b,
           LogicType c, Typeable c, LogicType d, Typeable d,
           LogicType e, Typeable e, LogicType f, Typeable f)
       => RuleM rel ts ('St n steps cc) ('St ((((((n + 1) + 1) + 1) + 1) + 1) + 1) steps cc)
            (T '[n] a rel, T '[n + 1] b rel, T '[(n + 1) + 1] c rel,
             T '[((n + 1) + 1) + 1] d rel, T '[(((n + 1) + 1) + 1) + 1] e rel,
             T '[((((n + 1) + 1) + 1) + 1) + 1] f rel)
fresh6 = Ix.do
  a <- fresh @a
  b <- fresh @b
  c <- fresh @c
  d <- fresh @d
  e <- fresh @e
  f <- fresh @f
  return (a, b, c, d, e, f)

-- | Declare the conclusion pattern
concl :: forall name modes rel vss ts n steps.
         ( InputVars modes vss ts
         , OutputVars modes vss ts
         , ToLTermList vss ts
         )
      => AppliedM rel name modes vss ts
      -> RuleM rel ts ('St n steps 'False)
                   ('St n (Snoc steps ('ConcStep name (ReqVars modes vss) (ProdVars modes vss))) 'True) ()
concl applied = liftF (ConclF applied)

-- | Declare a premise
prem :: forall name modes rel vss ts ts' n steps c.
        ( InputVars modes vss ts'
        , OutputVars modes vss ts'
        )
     => AppliedM rel name modes vss ts'
     -> RuleM rel ts ('St n steps c)
              ('St n (Snoc steps ('PremStep ('Goal name (ReqVars modes vss) (ProdVars modes vss)))) c) ()
prem applied = liftF (PremF applied)

-- | Declare negation-as-failure
neg :: forall name modes rel vss ts ts' n steps c.
       ( InputVars modes vss ts'
       , OutputVars modes vss ts'
       )
    => AppliedM rel name modes vss ts'
    -> RuleM rel ts ('St n steps c)
             ('St n (Snoc steps ('NegStep (AllVars modes vss))) c) ()
neg applied = liftF (NegF applied)

-- | Unification constraint
infix 4 ===
(===) :: forall a rel ts vs1 vs2 n steps c.
         (LogicType a, Typeable a)
      => T vs1 a rel -> T vs2 a rel
      -> RuleM rel ts ('St n steps c)
                   ('St n (Snoc steps ('PremStep ('Goal "==" (Union vs1 vs2) '[]))) c) ()
(===) t1 t2 = liftF (UnifyF t1 t2)

-- | Disequality constraint
infix 4 =/=
(=/=) :: forall a rel ts vs1 vs2 n steps c.
         (LogicType a, Typeable a)
      => T vs1 a rel -> T vs2 a rel
      -> RuleM rel ts ('St n steps c)
                   ('St n (Snoc steps ('PremStep ('Goal "=/=" (Union vs1 vs2) '[]))) c) ()
(=/=) t1 t2 = liftF (NeqF t1 t2)

-- | Lift an immediate rel action
liftRel :: rel a -> RuleM rel ts s s a
liftRel action = liftF (LiftRelF action)

-- | Lift a deferred rel action
liftRelDeferred :: rel () -> RuleM rel ts s s ()
liftRelDeferred action = liftF (LiftRelDeferredF action)

--------------------------------------------------------------------------------
-- Moded Rules
--------------------------------------------------------------------------------

-- | A moded rule (result of ruleM)
--
-- Uses existential quantification to hide the final state
data ModedRule rel (ts :: [Type]) = forall n steps.
  ModedRule
    { mrName :: String
    , mrBody :: IxFree (RuleF rel ts) ('St 0 '[] 'False) ('St n steps 'True) ()
    }

-- | Create a moded rule with compile-time schedule checking
--
-- The CheckSchedule constraint fires at compile time, ensuring
-- a valid execution order exists.
ruleM :: forall name rel n steps ts.
         ( RedexNeg rel
         , CheckSchedule name steps
         )
      => String
      -> RuleM rel ts ('St 0 '[] 'False) ('St n steps 'True) ()
      -> ModedRule rel ts
ruleM name body = ModedRule name body

--------------------------------------------------------------------------------
-- Moded Type Wrappers
--------------------------------------------------------------------------------

-- | Phantom wrapper for input mode
data In (a :: Type)

-- | Phantom wrapper for output mode
data Out (a :: Type)

-- | Extract mode from wrapper
type family GetMode (x :: Type) :: Mode where
  GetMode (In _)  = 'I
  GetMode (Out _) = 'O

-- | Extract type from wrapper
type family GetType (x :: Type) :: Type where
  GetType (In a)  = a
  GetType (Out a) = a

--------------------------------------------------------------------------------
-- Judgment Type Aliases
--------------------------------------------------------------------------------

type Judgment1 rel (name :: Symbol) (modes :: [Mode]) (t1 :: Type) =
  forall vs1.
    ( InputVars modes '[vs1] '[t1]
    , OutputVars modes '[vs1] '[t1]
    ) =>
    T vs1 t1 rel -> AppliedM rel name modes '[vs1] '[t1]

type Judgment2 rel (name :: Symbol) (modes :: [Mode]) (t1 :: Type) (t2 :: Type) =
  forall vs1 vs2.
    ( InputVars modes '[vs1, vs2] '[t1, t2]
    , OutputVars modes '[vs1, vs2] '[t1, t2]
    ) =>
    T vs1 t1 rel -> T vs2 t2 rel -> AppliedM rel name modes '[vs1, vs2] '[t1, t2]

type Judgment3 rel (name :: Symbol) (modes :: [Mode]) (t1 :: Type) (t2 :: Type) (t3 :: Type) =
  forall vs1 vs2 vs3.
    ( InputVars modes '[vs1, vs2, vs3] '[t1, t2, t3]
    , OutputVars modes '[vs1, vs2, vs3] '[t1, t2, t3]
    ) =>
    T vs1 t1 rel -> T vs2 t2 rel -> T vs3 t3 rel ->
    AppliedM rel name modes '[vs1, vs2, vs3] '[t1, t2, t3]

type Judgment4 rel (name :: Symbol) (modes :: [Mode]) (t1 :: Type) (t2 :: Type) (t3 :: Type) (t4 :: Type) =
  forall vs1 vs2 vs3 vs4.
    ( InputVars modes '[vs1, vs2, vs3, vs4] '[t1, t2, t3, t4]
    , OutputVars modes '[vs1, vs2, vs3, vs4] '[t1, t2, t3, t4]
    ) =>
    T vs1 t1 rel -> T vs2 t2 rel -> T vs3 t3 rel -> T vs4 t4 rel ->
    AppliedM rel name modes '[vs1, vs2, vs3, vs4] '[t1, t2, t3, t4]

type Judgment5 rel (name :: Symbol) (modes :: [Mode]) (t1 :: Type) (t2 :: Type) (t3 :: Type) (t4 :: Type) (t5 :: Type) =
  forall vs1 vs2 vs3 vs4 vs5.
    ( InputVars modes '[vs1, vs2, vs3, vs4, vs5] '[t1, t2, t3, t4, t5]
    , OutputVars modes '[vs1, vs2, vs3, vs4, vs5] '[t1, t2, t3, t4, t5]
    ) =>
    T vs1 t1 rel -> T vs2 t2 rel -> T vs3 t3 rel -> T vs4 t4 rel -> T vs5 t5 rel ->
    AppliedM rel name modes '[vs1, vs2, vs3, vs4, vs5] '[t1, t2, t3, t4, t5]

type Judgment6 rel (name :: Symbol) (modes :: [Mode]) (t1 :: Type) (t2 :: Type) (t3 :: Type) (t4 :: Type) (t5 :: Type) (t6 :: Type) =
  forall vs1 vs2 vs3 vs4 vs5 vs6.
    ( InputVars modes '[vs1, vs2, vs3, vs4, vs5, vs6] '[t1, t2, t3, t4, t5, t6]
    , OutputVars modes '[vs1, vs2, vs3, vs4, vs5, vs6] '[t1, t2, t3, t4, t5, t6]
    ) =>
    T vs1 t1 rel -> T vs2 t2 rel -> T vs3 t3 rel -> T vs4 t4 rel -> T vs5 t5 rel -> T vs6 t6 rel ->
    AppliedM rel name modes '[vs1, vs2, vs3, vs4, vs5, vs6] '[t1, t2, t3, t4, t5, t6]

--------------------------------------------------------------------------------
-- Moded Judgment Aliases
--------------------------------------------------------------------------------

type MJudgment1 rel (name :: Symbol) m1 =
  Judgment1 rel name '[GetMode m1] (GetType m1)

type MJudgment2 rel (name :: Symbol) m1 m2 =
  Judgment2 rel name '[GetMode m1, GetMode m2] (GetType m1) (GetType m2)

type MJudgment3 rel (name :: Symbol) m1 m2 m3 =
  Judgment3 rel name '[GetMode m1, GetMode m2, GetMode m3]
                     (GetType m1) (GetType m2) (GetType m3)

type MJudgment4 rel (name :: Symbol) m1 m2 m3 m4 =
  Judgment4 rel name '[GetMode m1, GetMode m2, GetMode m3, GetMode m4]
                     (GetType m1) (GetType m2) (GetType m3) (GetType m4)

type MJudgment5 rel (name :: Symbol) m1 m2 m3 m4 m5 =
  Judgment5 rel name '[GetMode m1, GetMode m2, GetMode m3, GetMode m4, GetMode m5]
                     (GetType m1) (GetType m2) (GetType m3) (GetType m4) (GetType m5)

type MJudgment6 rel (name :: Symbol) m1 m2 m3 m4 m5 m6 =
  Judgment6 rel name '[GetMode m1, GetMode m2, GetMode m3, GetMode m4, GetMode m5, GetMode m6]
                     (GetType m1) (GetType m2) (GetType m3) (GetType m4) (GetType m5) (GetType m6)

--------------------------------------------------------------------------------
-- Judgment Definition Helpers
--------------------------------------------------------------------------------

-- | Define a unary moded judgment
mjudge1 :: forall name modes rel t1.
           (Redex rel, KnownSymbol name, LogicType t1, SingModeList modes)
        => ModeList modes
        -> [ModedRule rel '[t1]]
        -> Judgment1 rel name modes t1
mjudge1 modes rules t1 =
  let args = t1 :! ANil
  in mkAppliedM @name modes args rules

-- | Define a binary moded judgment
mjudge2 :: forall name modes rel t1 t2.
           (Redex rel, KnownSymbol name, LogicType t1, LogicType t2, SingModeList modes)
        => ModeList modes
        -> [ModedRule rel '[t1, t2]]
        -> Judgment2 rel name modes t1 t2
mjudge2 modes rules t1 t2 =
  let args = t1 :! t2 :! ANil
  in mkAppliedM @name modes args rules

-- | Define a ternary moded judgment
mjudge3 :: forall name modes rel t1 t2 t3.
           (Redex rel, KnownSymbol name, LogicType t1, LogicType t2, LogicType t3, SingModeList modes)
        => ModeList modes
        -> [ModedRule rel '[t1, t2, t3]]
        -> Judgment3 rel name modes t1 t2 t3
mjudge3 modes rules t1 t2 t3 =
  let args = t1 :! t2 :! t3 :! ANil
  in mkAppliedM @name modes args rules

mjudge4 :: forall name modes rel t1 t2 t3 t4.
           (Redex rel, KnownSymbol name, LogicType t1, LogicType t2, LogicType t3, LogicType t4, SingModeList modes)
        => ModeList modes
        -> [ModedRule rel '[t1, t2, t3, t4]]
        -> Judgment4 rel name modes t1 t2 t3 t4
mjudge4 modes rules t1 t2 t3 t4 =
  let args = t1 :! t2 :! t3 :! t4 :! ANil
  in mkAppliedM @name modes args rules

mjudge5 :: forall name modes rel t1 t2 t3 t4 t5.
           (Redex rel, KnownSymbol name, LogicType t1, LogicType t2, LogicType t3, LogicType t4, LogicType t5, SingModeList modes)
        => ModeList modes
        -> [ModedRule rel '[t1, t2, t3, t4, t5]]
        -> Judgment5 rel name modes t1 t2 t3 t4 t5
mjudge5 modes rules t1 t2 t3 t4 t5 =
  let args = t1 :! t2 :! t3 :! t4 :! t5 :! ANil
  in mkAppliedM @name modes args rules

mjudge6 :: forall name modes rel t1 t2 t3 t4 t5 t6.
           (Redex rel, KnownSymbol name, LogicType t1, LogicType t2, LogicType t3, LogicType t4, LogicType t5, LogicType t6, SingModeList modes)
        => ModeList modes
        -> [ModedRule rel '[t1, t2, t3, t4, t5, t6]]
        -> Judgment6 rel name modes t1 t2 t3 t4 t5 t6
mjudge6 modes rules t1 t2 t3 t4 t5 t6 =
  let args = t1 :! t2 :! t3 :! t4 :! t5 :! t6 :! ANil
  in mkAppliedM @name modes args rules

-- | Helper to build AppliedM
mkAppliedM :: forall name modes rel vss ts.
              ( Redex rel, KnownSymbol name
              , InputVars modes vss ts
              , OutputVars modes vss ts
              , ToLTermList vss ts
              , SingModeList modes
              )
           => ModeList modes
           -> TArgs vss ts rel
           -> [ModedRule rel ts]
           -> AppliedM rel name modes vss ts
mkAppliedM modes args rules = AppliedM
  { amGoal = asum
      [ runModedRule args rule
      | rule <- rules
      ]
  , amName = symbolVal (Proxy @name)
  , amArgs = toLTermList args
  , amReqVars = inputVars modes args
  , amProdVars = outputVars modes args
  }

-- | Run a moded rule, handling the existential types
runModedRule :: (Redex rel, ToLTermList vss ts)
             => TArgs vss ts rel
             -> ModedRule rel ts
             -> rel ()
runModedRule args (ModedRule name body) =
  call_ Opaque $ Relation name (captureArgs (toLTermList args)) Prelude.$
    interpretRule args body

-- | Placeholder for interpretation (will be implemented in Interp modules)
interpretRule :: (Redex rel, ToLTermList vss ts)
              => TArgs vss ts rel
              -> IxFree (RuleF rel ts) ('St 0 '[] 'False) ('St n steps 'True) ()
              -> rel ()
interpretRule = error "interpretRule: use specific interpreter module"

--------------------------------------------------------------------------------
-- defJudge helpers (with scoped rule builder)
--------------------------------------------------------------------------------

-- | Unify LTermLists element-wise
class UnifyLList rel ts where
  unifyLList :: LTermList rel ts -> LTermList rel ts -> rel ()

instance Redex rel => UnifyLList rel '[] where
  unifyLList TNil TNil = pure ()

instance (LogicType t, Redex rel, UnifyLList rel ts) => UnifyLList rel (t ': ts) where
  unifyLList (x :> xs) (y :> ys) = unify x y Prelude.>> unifyLList xs ys

defJudge1 :: forall name modes rel t1.
             (RedexNeg rel, KnownSymbol name, LogicType t1, Typeable t1, UnifyLList rel '[t1], SingModeList modes)
          => ((forall n steps. CheckSchedule name steps
               => String -> RuleM rel '[t1] ('St 0 '[] 'False) ('St n steps 'True) ()
               -> ModedRule rel '[t1])
              -> [ModedRule rel '[t1]])
          -> Judgment1 rel name modes t1
defJudge1 mkRules = mjudge1 singModeList (mkRules rule)
  where
    rule :: forall n steps. CheckSchedule name steps
         => String -> RuleM rel '[t1] ('St 0 '[] 'False) ('St n steps 'True) ()
         -> ModedRule rel '[t1]
    rule = ruleM @name

defJudge2 :: forall name modes rel t1 t2.
             (RedexNeg rel, KnownSymbol name, LogicType t1, Typeable t1, LogicType t2, Typeable t2, UnifyLList rel '[t1, t2], SingModeList modes)
          => ((forall n steps. CheckSchedule name steps
               => String -> RuleM rel '[t1, t2] ('St 0 '[] 'False) ('St n steps 'True) ()
               -> ModedRule rel '[t1, t2])
              -> [ModedRule rel '[t1, t2]])
          -> Judgment2 rel name modes t1 t2
defJudge2 mkRules = mjudge2 singModeList (mkRules rule)
  where
    rule :: forall n steps. CheckSchedule name steps
         => String -> RuleM rel '[t1, t2] ('St 0 '[] 'False) ('St n steps 'True) ()
         -> ModedRule rel '[t1, t2]
    rule = ruleM @name

defJudge3 :: forall name modes rel t1 t2 t3.
             (RedexNeg rel, KnownSymbol name, LogicType t1, Typeable t1, LogicType t2, Typeable t2, LogicType t3, Typeable t3, UnifyLList rel '[t1, t2, t3], SingModeList modes)
          => ((forall n steps. CheckSchedule name steps
               => String -> RuleM rel '[t1, t2, t3] ('St 0 '[] 'False) ('St n steps 'True) ()
               -> ModedRule rel '[t1, t2, t3])
              -> [ModedRule rel '[t1, t2, t3]])
          -> Judgment3 rel name modes t1 t2 t3
defJudge3 mkRules = mjudge3 singModeList (mkRules rule)
  where
    rule :: forall n steps. CheckSchedule name steps
         => String -> RuleM rel '[t1, t2, t3] ('St 0 '[] 'False) ('St n steps 'True) ()
         -> ModedRule rel '[t1, t2, t3]
    rule = ruleM @name

defJudge4 :: forall name modes rel t1 t2 t3 t4.
             (RedexNeg rel, KnownSymbol name, LogicType t1, Typeable t1, LogicType t2, Typeable t2, LogicType t3, Typeable t3, LogicType t4, Typeable t4, UnifyLList rel '[t1, t2, t3, t4], SingModeList modes)
          => ((forall n steps. CheckSchedule name steps
               => String -> RuleM rel '[t1, t2, t3, t4] ('St 0 '[] 'False) ('St n steps 'True) ()
               -> ModedRule rel '[t1, t2, t3, t4])
              -> [ModedRule rel '[t1, t2, t3, t4]])
          -> Judgment4 rel name modes t1 t2 t3 t4
defJudge4 mkRules = mjudge4 singModeList (mkRules rule)
  where
    rule :: forall n steps. CheckSchedule name steps
         => String -> RuleM rel '[t1, t2, t3, t4] ('St 0 '[] 'False) ('St n steps 'True) ()
         -> ModedRule rel '[t1, t2, t3, t4]
    rule = ruleM @name

defJudge5 :: forall name modes rel t1 t2 t3 t4 t5.
             (RedexNeg rel, KnownSymbol name, LogicType t1, Typeable t1, LogicType t2, Typeable t2, LogicType t3, Typeable t3, LogicType t4, Typeable t4, LogicType t5, Typeable t5, UnifyLList rel '[t1, t2, t3, t4, t5], SingModeList modes)
          => ((forall n steps. CheckSchedule name steps
               => String -> RuleM rel '[t1, t2, t3, t4, t5] ('St 0 '[] 'False) ('St n steps 'True) ()
               -> ModedRule rel '[t1, t2, t3, t4, t5])
              -> [ModedRule rel '[t1, t2, t3, t4, t5]])
          -> Judgment5 rel name modes t1 t2 t3 t4 t5
defJudge5 mkRules = mjudge5 singModeList (mkRules rule)
  where
    rule :: forall n steps. CheckSchedule name steps
         => String -> RuleM rel '[t1, t2, t3, t4, t5] ('St 0 '[] 'False) ('St n steps 'True) ()
         -> ModedRule rel '[t1, t2, t3, t4, t5]
    rule = ruleM @name

defJudge6 :: forall name modes rel t1 t2 t3 t4 t5 t6.
             (RedexNeg rel, KnownSymbol name, LogicType t1, Typeable t1, LogicType t2, Typeable t2, LogicType t3, Typeable t3, LogicType t4, Typeable t4, LogicType t5, Typeable t5, LogicType t6, Typeable t6, UnifyLList rel '[t1, t2, t3, t4, t5, t6], SingModeList modes)
          => ((forall n steps. CheckSchedule name steps
               => String -> RuleM rel '[t1, t2, t3, t4, t5, t6] ('St 0 '[] 'False) ('St n steps 'True) ()
               -> ModedRule rel '[t1, t2, t3, t4, t5, t6])
              -> [ModedRule rel '[t1, t2, t3, t4, t5, t6]])
          -> Judgment6 rel name modes t1 t2 t3 t4 t5 t6
defJudge6 mkRules = mjudge6 singModeList (mkRules rule)
  where
    rule :: forall n steps. CheckSchedule name steps
         => String -> RuleM rel '[t1, t2, t3, t4, t5, t6] ('St 0 '[] 'False) ('St n steps 'True) ()
         -> ModedRule rel '[t1, t2, t3, t4, t5, t6]
    rule = ruleM @name

--------------------------------------------------------------------------------
-- toApplied (for running queries)
--------------------------------------------------------------------------------

-- | Dummy Applied type for compatibility
data Applied rel (ts :: [Type]) = Applied
  { appliedArgs :: LTermList rel ts
  , appliedGoal :: rel ()
  , appliedName :: String
  }

-- | Convert AppliedM to Applied
toApplied :: AppliedM rel name modes vss ts -> Applied rel ts
toApplied (AppliedM goal name args _ _) = Applied args goal name
