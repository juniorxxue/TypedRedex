{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

-- | Mode-guided static scheduling for TypedRedex.
--
-- This module provides statically-checked mode annotations that:
--
-- * Declare which positions are inputs (I) vs outputs (O)
-- * Verify at compile time that a valid execution schedule exists
-- * Execute premises in source order (runtime scheduling planned)
--
-- = Usage
--
-- @
-- {-# LANGUAGE QualifiedDo, DataKinds, TypeApplications #-}
-- import qualified TypedRedex.DSL.Moded as R
--
-- -- Define a moded judgment (callable function)
-- lookupM :: (Redex rel, ToLTermList vss '[Ctx, Nat, Ty])
--         => TArgs vss '[Ctx, Nat, Ty] rel -> AppliedM rel \"lookup\" '[I, I, O] vss '[Ctx, Nat, Ty]
-- lookupM = mjudge (I :* I :* O :* MNil)
--   [ ruleM \@\"lookup\" \"here\" $ \\_ -> R.do
--       ty <- R.fresh
--       rest <- R.fresh
--       R.concl $ lookupM (consM ty rest :! zroM :! ty :! ANil)
--
--   , ruleM \@\"lookup\" \"there\" $ \\_ -> R.do
--       ty <- R.fresh
--       ty' <- R.fresh
--       rest <- R.fresh
--       n' <- R.fresh
--       R.concl $ lookupM (consM ty' rest :! sucM n' :! ty :! ANil)
--       R.prem $ lookupM (rest :! n' :! ty :! ANil)
--   ]
-- @
module TypedRedex.DSL.Moded
  ( -- * Modes
    Mode(..)
  , ModeList(..)
    -- * Moded terms
  , T(..)
  , ground
  , lift1, lift2, lift3
    -- * Argument lists
  , TArgs(..)
    -- * Moded judgments
  , AppliedM(..)
  , mjudge, mjudge1, mjudge2, mjudge3
  , toApplied
  , ToLTermList(..)
    -- * Rule building
  , RuleM
  , ruleM
  , ModedRule(..)
    -- * Rule operations
  , fresh
  , prem
  , concl
  , liftRel
    -- * QualifiedDo operators
  , return, (>>=), (>>)
    -- * Type-level machinery
  , CheckSchedule
  , Union
  ) where

import Prelude hiding ((>>=), (>>), return)
import qualified Prelude
import Data.Kind (Constraint, Type)
import GHC.TypeLits (TypeError, ErrorMessage(..), Symbol, KnownSymbol, symbolVal)
import GHC.TypeNats (Nat, type (+))
import Data.Proxy (Proxy(..))
import Control.Applicative (asum)

import TypedRedex.Core.Internal.Redex (Redex(..), Relation(..), FreshType(..))
import TypedRedex.Core.Internal.Logic (Logic(..), LogicType(..))
import TypedRedex.DSL.Fresh (LTerm)
import TypedRedex.DSL.Define (Applied(..), LTermList(..))
import TypedRedex.Core.Internal.Relation (call, (<=>))

--------------------------------------------------------------------------------
-- Modes
--------------------------------------------------------------------------------

data Mode = I | O
  deriving (Eq, Show)

data ModeList (ms :: [Mode]) where
  MNil  :: ModeList '[]
  (:*)  :: Mode -> ModeList ms -> ModeList (m ': ms)
infixr 5 :*

--------------------------------------------------------------------------------
-- Moded Terms
--------------------------------------------------------------------------------

-- | Term with type-level variable tracking.
newtype T (vs :: [Nat]) a (rel :: Type -> Type) = T { unT :: LTerm a rel }

ground :: LTerm a rel -> T '[] a rel
ground = T

lift1 :: (LTerm a rel -> LTerm b rel) -> T vs a rel -> T vs b rel
lift1 f (T x) = T (f x)

lift2 :: (LTerm a rel -> LTerm b rel -> LTerm c rel)
      -> T vs1 a rel -> T vs2 b rel -> T (Union vs1 vs2) c rel
lift2 f (T x) (T y) = T (f x y)

lift3 :: (LTerm a rel -> LTerm b rel -> LTerm c rel -> LTerm d rel)
      -> T vs1 a rel -> T vs2 b rel -> T vs3 c rel
      -> T (Union vs1 (Union vs2 vs3)) d rel
lift3 f (T x) (T y) (T z) = T (f x y z)

--------------------------------------------------------------------------------
-- Type-level Sets
--------------------------------------------------------------------------------

type family If (b :: Bool) (t :: k) (f :: k) :: k where
  If 'True  t _ = t
  If 'False _ f = f

type family And (a :: Bool) (b :: Bool) :: Bool where
  And 'True b = b
  And 'False _ = 'False

type family Elem (x :: Nat) (xs :: [Nat]) :: Bool where
  Elem _ '[] = 'False
  Elem x (x ': _) = 'True
  Elem x (_ ': xs) = Elem x xs

type family Insert (x :: Nat) (xs :: [Nat]) :: [Nat] where
  Insert x xs = If (Elem x xs) xs (x ': xs)

type family Union (xs :: [Nat]) (ys :: [Nat]) :: [Nat] where
  Union '[] ys = ys
  Union (x ': xs) ys = Union xs (Insert x ys)

type family Subset (xs :: [Nat]) (ys :: [Nat]) :: Bool where
  Subset '[] _ = 'True
  Subset (x ': xs) ys = And (Elem x ys) (Subset xs ys)

type family Diff (xs :: [Nat]) (ys :: [Nat]) :: [Nat] where
  Diff '[] _ = '[]
  Diff (x ': xs) ys = If (Elem x ys) (Diff xs ys) (x ': Diff xs ys)

type family Snoc (xs :: [k]) (x :: k) :: [k] where
  Snoc '[] x = '[x]
  Snoc (y ': ys) x = y ': Snoc ys x

--------------------------------------------------------------------------------
-- Typed Argument Lists
--------------------------------------------------------------------------------

-- | Typed argument list with var-set tracking.
data TArgs (vss :: [[Nat]]) (ts :: [Type]) (rel :: Type -> Type) where
  ANil :: TArgs '[] '[] rel
  (:!) :: T vs a rel -> TArgs vss ts rel -> TArgs (vs ': vss) (a ': ts) rel

infixr 5 :!

-- | Extract var-sets from argument list.
type family ArgVars (vss :: [[Nat]]) :: [[Nat]] where
  ArgVars vss = vss

--------------------------------------------------------------------------------
-- Mode Analysis
--------------------------------------------------------------------------------

type family ReqVars (modes :: [Mode]) (vss :: [[Nat]]) :: [Nat] where
  ReqVars '[] '[] = '[]
  ReqVars ('I ': ms) (vs ': vss) = Union vs (ReqVars ms vss)
  ReqVars ('O ': ms) (_ ': vss) = ReqVars ms vss
  ReqVars _ _ = TypeError ('Text "Mode/arg mismatch")

type family ProdVars (modes :: [Mode]) (vss :: [[Nat]]) :: [Nat] where
  ProdVars '[] '[] = '[]
  ProdVars ('I ': ms) (_ ': vss) = ProdVars ms vss
  ProdVars ('O ': ms) (vs ': vss) = Union vs (ProdVars ms vss)
  ProdVars _ _ = TypeError ('Text "Mode/arg mismatch")

--------------------------------------------------------------------------------
-- Rule State Machine
--------------------------------------------------------------------------------

data Goal = Goal Symbol [Nat] [Nat]
data Step = ConcStep Symbol [Nat] | PremStep Goal
data St = St Nat [Step] Bool

-- | Rule monad with access to caller's arguments.
-- 'ts' is the type list of the enclosing judgment.
newtype RuleM (rel :: Type -> Type) (ts :: [Type]) (s :: St) (t :: St) a = RuleM
  { runRuleM :: LTermList rel ts -> rel a }

return :: Redex rel => a -> RuleM rel ts s s a
return a = RuleM $ \_ -> pure a

(>>=) :: Redex rel => RuleM rel ts s t a -> (a -> RuleM rel ts t u b) -> RuleM rel ts s u b
RuleM m >>= f = RuleM $ \args -> m args Prelude.>>= (\a -> runRuleM (f a) args)

(>>) :: Redex rel => RuleM rel ts s t a -> RuleM rel ts t u b -> RuleM rel ts s u b
m >> k = m >>= \_ -> k

--------------------------------------------------------------------------------
-- Fresh
--------------------------------------------------------------------------------

fresh :: forall a rel ts n steps c.
         (Redex rel, LogicType a)
      => RuleM rel ts ('St n steps c) ('St (n + 1) steps c) (T '[n] a rel)
fresh = RuleM $ \_ -> fresh_ FreshVar (pure . T . Free)

--------------------------------------------------------------------------------
-- Lifting rel actions
--------------------------------------------------------------------------------

-- | Lift an arbitrary 'rel' action into 'RuleM'.
--
-- This is useful for operations that don't participate in mode tracking,
-- such as generating fresh nominal atoms or calling 'instantiateTo'.
--
-- @
-- -- Generate a fresh nominal atom (no mode tracking)
-- x <- liftRel freshNom
--
-- -- Call instantiateTo (inline operation, no mode tracking)
-- liftRel $ instantiateTo tyBnd tyArg result
-- @
liftRel :: rel a -> RuleM rel ts s s a
liftRel action = RuleM $ \_ -> action

--------------------------------------------------------------------------------
-- Moded Judgments
--------------------------------------------------------------------------------

-- | Result of applying a moded judgment. Carries mode info at the type level.
data AppliedM rel (name :: Symbol) (modes :: [Mode]) (vss :: [[Nat]]) (ts :: [Type]) = AppliedM
  { amGoal :: rel ()
  , amName :: String
  , amArgs :: LTermList rel ts
  }

-- | Convert TArgs to LTermList (strip variable tracking).
class ToLTermList (vss :: [[Nat]]) (ts :: [Type]) where
  toLTermList :: TArgs vss ts rel -> LTermList rel ts

instance ToLTermList '[] '[] where
  toLTermList ANil = TNil

instance (LogicType t, ToLTermList vss ts) => ToLTermList (vs ': vss) (t ': ts) where
  toLTermList (T x :! xs) = x :> toLTermList xs

-- | A moded judgment definition.
data MJudgeDef rel (name :: Symbol) (modes :: [Mode]) (ts :: [Type]) = MJudgeDef
  { mjdName  :: String
  , mjdRules :: [ModedRule rel ts]
  }

-- | Define a moded judgment. Returns a function that takes TArgs.
mjudge :: forall name modes rel ts.
          (Redex rel, KnownSymbol name)
       => ModeList modes
       -> [ModedRule rel ts]
       -> (forall vss. ToLTermList vss ts => TArgs vss ts rel -> AppliedM rel name modes vss ts)
mjudge _modes rules = \args -> AppliedM
  { amGoal = asum [ call $ Relation name [] (body args)
                  | ModedRule name body <- rules
                  ]
  , amName = symbolVal (Proxy @name)
  , amArgs = toLTermList args
  }

-- | Define a unary moded judgment with curried syntax.
mjudge1 :: forall name modes rel t1.
           (Redex rel, KnownSymbol name, LogicType t1)
        => ModeList modes
        -> [ModedRule rel '[t1]]
        -> (forall vs1. T vs1 t1 rel -> AppliedM rel name modes '[vs1] '[t1])
mjudge1 modes rules = \(T x1) ->
  let args = T x1 :! ANil
  in mjudge modes rules args

-- | Define a binary moded judgment with curried syntax.
mjudge2 :: forall name modes rel t1 t2.
           (Redex rel, KnownSymbol name, LogicType t1, LogicType t2)
        => ModeList modes
        -> [ModedRule rel '[t1, t2]]
        -> (forall vs1 vs2. T vs1 t1 rel -> T vs2 t2 rel -> AppliedM rel name modes '[vs1, vs2] '[t1, t2])
mjudge2 modes rules = \(T x1) (T x2) ->
  let args = T x1 :! T x2 :! ANil
  in mjudge modes rules args

-- | Define a ternary moded judgment with curried syntax.
mjudge3 :: forall name modes rel t1 t2 t3.
           (Redex rel, KnownSymbol name, LogicType t1, LogicType t2, LogicType t3)
        => ModeList modes
        -> [ModedRule rel '[t1, t2, t3]]
        -> (forall vs1 vs2 vs3. T vs1 t1 rel -> T vs2 t2 rel -> T vs3 t3 rel
            -> AppliedM rel name modes '[vs1, vs2, vs3] '[t1, t2, t3])
mjudge3 modes rules = \(T x1) (T x2) (T x3) ->
  let args = T x1 :! T x2 :! T x3 :! ANil
  in mjudge modes rules args

-- | Convert AppliedM to Applied for running queries.
toApplied :: AppliedM rel name modes vss ts -> Applied rel ts
toApplied (AppliedM goal name args) = Applied args goal name

modeListToList :: ModeList ms -> [Mode]
modeListToList MNil = []
modeListToList (m :* ms) = m : modeListToList ms

--------------------------------------------------------------------------------
-- Conclusion and Premise
--------------------------------------------------------------------------------

-- | Unify two LTermLists element-wise.
class UnifyLList rel ts where
  unifyLList :: LTermList rel ts -> LTermList rel ts -> rel ()

instance Redex rel => UnifyLList rel '[] where
  unifyLList TNil TNil = pure ()

instance (LogicType t, Redex rel, UnifyLList rel ts) => UnifyLList rel (t ': ts) where
  unifyLList (x :> xs) (y :> ys) = (x <=> y) Prelude.>> unifyLList xs ys

-- | Declare conclusion. Unifies pattern with caller's arguments.
concl :: forall name modes rel vss ts n steps.
         (Redex rel, UnifyLList rel ts)
      => AppliedM rel name modes vss ts
      -> RuleM rel ts ('St n steps 'False)
                   ('St n (Snoc steps ('ConcStep name (ReqVars modes vss))) 'True) ()
concl applied = RuleM $ \callerArgs -> unifyLList (amArgs applied) callerArgs

-- | Declare premise. Executes the judgment's goal.
prem :: forall name modes rel vss ts ts' n steps c.
        Redex rel
     => AppliedM rel name modes vss ts'
     -> RuleM rel ts ('St n steps c)
                  ('St n (Snoc steps ('PremStep ('Goal name (ReqVars modes vss) (ProdVars modes vss)))) c) ()
prem applied = RuleM $ \_ -> amGoal applied

-- | Unify two argument lists.
class UnifyTArgs rel ts where
  unifyTArgs :: TArgs vss1 ts rel -> TArgs vss2 ts rel -> rel ()

instance Redex rel => UnifyTArgs rel '[] where
  unifyTArgs ANil ANil = pure ()

instance (LogicType t, Redex rel, UnifyTArgs rel ts) => UnifyTArgs rel (t ': ts) where
  unifyTArgs (T x :! xs) (T y :! ys) = (x <=> y) Prelude.>> unifyTArgs xs ys

--------------------------------------------------------------------------------
-- Schedule Checking
--------------------------------------------------------------------------------

type family ConclVars (steps :: [Step]) :: [Nat] where
  ConclVars ('ConcStep _ vs ': _) = vs
  ConclVars (_ ': rest) = ConclVars rest
  ConclVars '[] = TypeError ('Text "No conclusion in rule")

type family PremGoals (steps :: [Step]) :: [Goal] where
  PremGoals '[] = '[]
  PremGoals ('PremStep g ': rest) = g ': PremGoals rest
  PremGoals ('ConcStep _ _ ': rest) = PremGoals rest

type family Ready (avail :: [Nat]) (g :: Goal) :: Bool where
  Ready avail ('Goal _ req _) = Subset req avail

type family SelectReady (avail :: [Nat]) (gs :: [Goal]) :: Maybe (Goal, [Goal]) where
  SelectReady _ '[] = 'Nothing
  SelectReady avail (g ': gs) =
    If (Ready avail g) ('Just '(g, gs)) (PrependMaybe g (SelectReady avail gs))

type family PrependMaybe (g :: Goal) (m :: Maybe (Goal, [Goal])) :: Maybe (Goal, [Goal]) where
  PrependMaybe _ 'Nothing = 'Nothing
  PrependMaybe g ('Just '(g1, rest)) = 'Just '(g1, g ': rest)

data SolveResult = Solved | Stuck [Nat] [Goal]

type family Solve (avail :: [Nat]) (gs :: [Goal]) :: SolveResult where
  Solve _ '[] = 'Solved
  Solve avail gs = SolveStep (SelectReady avail gs) avail gs

type family SolveStep (m :: Maybe (Goal, [Goal])) (avail :: [Nat]) (gs :: [Goal]) :: SolveResult where
  SolveStep 'Nothing avail gs = 'Stuck avail gs
  SolveStep ('Just '( 'Goal _ _ prod, rest)) avail _ = Solve (Union avail prod) rest

type family CheckSchedule (name :: Symbol) (steps :: [Step]) :: Constraint where
  CheckSchedule name steps = CheckResult name steps (Solve (ConclVars steps) (PremGoals steps))

type family CheckResult (name :: Symbol) (steps :: [Step]) (r :: SolveResult) :: Constraint where
  CheckResult _ _ 'Solved = ()
  CheckResult name steps ('Stuck avail gs) = TypeError
    ( 'Text "Mode error in \"" ':<>: 'Text name ':<>: 'Text "\":"
        ':$$: 'Text "  grounded: " ':<>: 'ShowType avail
        ':$$: 'Text "  blocked:"
        ':$$: ShowBlocked avail gs
    )

type family ShowBlocked (avail :: [Nat]) (gs :: [Goal]) :: ErrorMessage where
  ShowBlocked _ '[] = 'Text ""
  ShowBlocked avail ('Goal name req _ ': rest) =
    ('Text "    " ':<>: 'Text name ':<>: 'Text " needs " ':<>: 'ShowType (Diff req avail))
      ':$$: ShowBlocked avail rest

--------------------------------------------------------------------------------
-- Moded Rules
--------------------------------------------------------------------------------

-- | A moded rule.
data ModedRule rel (ts :: [Type]) = ModedRule
  { mrName :: String
  , mrBody :: forall vss. ToLTermList vss ts => TArgs vss ts rel -> rel ()
  }

-- | Create a moded rule. The rule body doesn't receive caller's args directly;
-- instead, 'concl' accesses them internally via the RuleM monad.
ruleM :: forall name rel n steps ts.
         (Redex rel, CheckSchedule name steps)
      => String
      -> RuleM rel ts ('St 0 '[] 'False) ('St n steps 'True) ()
      -> ModedRule rel ts
ruleM name body = ModedRule name $ \args -> runRuleM body (toLTermList args)
