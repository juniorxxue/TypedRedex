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
{-# LANGUAGE ExistentialQuantification #-}

-- | Mode-guided scheduling for TypedRedex.
--
-- This module provides mode annotations with runtime scheduling:
--
-- * Declare which positions are inputs (I) vs outputs (O)
-- * Verify at compile time that a valid execution schedule exists
-- * **Execute premises in mode-guided order at runtime** (not source order)
--
-- The order of @concl@ and @prem@ in a rule body does not matter—the
-- runtime scheduler determines the correct execution order based on modes.
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
--       -- Order doesn't matter! Runtime schedules correctly.
--       R.prem $ lookupM (rest :! n' :! ty :! ANil)
--       R.concl $ lookupM (consM ty' rest :! sucM n' :! ty :! ANil)
--   ]
-- @
module TypedRedex.DSL.Moded
  ( -- * Modes
    Mode(..)
  , ModeList(..)
  , SingModeList(..)
    -- * Moded terms
  , T(..)
  , ground
  , lift1, lift2, lift3
    -- * Argument lists
  , TArgs(..)
    -- * Moded judgments
  , AppliedM(..)
  , Judgment1
  , Judgment2
  , Judgment3
  , Judgment4
  , mjudge, mjudge1, mjudge2, mjudge3, mjudge4
  , defJudge1, defJudge2, defJudge3, defJudge4
  , toApplied
  , ToLTermList(..)
    -- * Rule building
  , RuleM
  , ruleM
  , ModedRule(..)
    -- * Rule operations
  , fresh, fresh2, fresh3, fresh4, fresh5, fresh6
  , prem
  , neg
  , concl
  , liftRel
  , liftRelDeferred
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
import qualified Data.Set as S
import Data.Set (Set)

import TypedRedex.Core.Internal.Redex (Redex(..), Relation(..), CapturedTerm(..), FreshType(..), RedexNeg)
import qualified TypedRedex.Core.Internal.Redex as R (neg)
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

-- | Singleton class: derive term-level ModeList from type-level list.
class SingModeList (ms :: [Mode]) where
  singModeList :: ModeList ms

instance SingModeList '[] where
  singModeList = MNil

instance SingModeList ms => SingModeList ('I ': ms) where
  singModeList = I :* singModeList

instance SingModeList ms => SingModeList ('O ': ms) where
  singModeList = O :* singModeList

--------------------------------------------------------------------------------
-- Moded Terms
--------------------------------------------------------------------------------

-- | Term with both type-level and runtime variable tracking.
--
-- The type-level @vs@ enables compile-time schedule verification.
-- The runtime @Set Int@ enables dynamic scheduling of premises.
data T (vs :: [Nat]) a (rel :: Type -> Type) = T
  { tVars :: Set Int       -- ^ Runtime variable IDs this term depends on
  , tTerm :: LTerm a rel   -- ^ The underlying logic term
  }

-- | Wrap a ground term (no variables).
ground :: LTerm a rel -> T '[] a rel
ground t = T S.empty t

-- | Lift a unary function, preserving variable tracking.
lift1 :: (LTerm a rel -> LTerm b rel) -> T vs a rel -> T vs b rel
lift1 f (T vars x) = T vars (f x)

-- | Lift a binary function, merging variable sets.
lift2 :: (LTerm a rel -> LTerm b rel -> LTerm c rel)
      -> T vs1 a rel -> T vs2 b rel -> T (Union vs1 vs2) c rel
lift2 f (T vars1 x) (T vars2 y) = T (S.union vars1 vars2) (f x y)

-- | Lift a ternary function, merging variable sets.
lift3 :: (LTerm a rel -> LTerm b rel -> LTerm c rel -> LTerm d rel)
      -> T vs1 a rel -> T vs2 b rel -> T vs3 c rel
      -> T (Union vs1 (Union vs2 vs3)) d rel
lift3 f (T vars1 x) (T vars2 y) (T vars3 z) = T (S.unions [vars1, vars2, vars3]) (f x y z)

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

-- | Get all runtime variable IDs from a TArgs.
class TArgsVars vss ts where
  targsVars :: TArgs vss ts rel -> Set Int

instance TArgsVars '[] '[] where
  targsVars ANil = S.empty

instance TArgsVars vss ts => TArgsVars (vs ': vss) (t ': ts) where
  targsVars (t :! ts) = S.union (tVars t) (targsVars ts)

-- | Get variable sets for input positions only.
class InputVars (ms :: [Mode]) vss ts where
  inputVars :: ModeList ms -> TArgs vss ts rel -> Set Int

instance InputVars '[] '[] '[] where
  inputVars MNil ANil = S.empty

instance InputVars ms vss ts => InputVars ('I ': ms) (vs ': vss) (t ': ts) where
  inputVars (_ :* ms) (t :! ts) = S.union (tVars t) (inputVars ms ts)

instance InputVars ms vss ts => InputVars ('O ': ms) (vs ': vss) (t ': ts) where
  inputVars (_ :* ms) (_ :! ts) = inputVars ms ts

-- | Get variable sets for output positions only.
class OutputVars (ms :: [Mode]) vss ts where
  outputVars :: ModeList ms -> TArgs vss ts rel -> Set Int

instance OutputVars '[] '[] '[] where
  outputVars MNil ANil = S.empty

instance OutputVars ms vss ts => OutputVars ('I ': ms) (vs ': vss) (t ': ts) where
  outputVars (_ :* ms) (_ :! ts) = outputVars ms ts

instance OutputVars ms vss ts => OutputVars ('O ': ms) (vs ': vss) (t ': ts) where
  outputVars (_ :* ms) (t :! ts) = S.union (tVars t) (outputVars ms ts)

--------------------------------------------------------------------------------
-- Mode Analysis
--------------------------------------------------------------------------------

type family ReqVars (modes :: [Mode]) (vss :: [[Nat]]) :: [Nat] where
  ReqVars '[] '[] = '[]
  ReqVars ('I ': ms) (vs ': vss) = Union vs (ReqVars ms vss)
  ReqVars ('O ': ms) (_ ': vss) = ReqVars ms vss
  ReqVars _ _ = TypeError ('Text "Mode list length does not match argument list length")

type family ProdVars (modes :: [Mode]) (vss :: [[Nat]]) :: [Nat] where
  ProdVars '[] '[] = '[]
  ProdVars ('I ': ms) (_ ': vss) = ProdVars ms vss
  ProdVars ('O ': ms) (vs ': vss) = Union vs (ProdVars ms vss)
  ProdVars _ _ = TypeError ('Text "Mode list length does not match argument list length")

-- | All variables in all positions (input + output).
-- Used for negation checking - all vars must be grounded.
type family AllVars (modes :: [Mode]) (vss :: [[Nat]]) :: [Nat] where
  AllVars modes vss = Union (ReqVars modes vss) (ProdVars modes vss)

--------------------------------------------------------------------------------
-- Rule State Machine (Runtime Scheduling)
--------------------------------------------------------------------------------

data Goal = Goal Symbol [Nat] [Nat]
data Step = ConcStep Symbol [Nat] | PremStep Goal | NegStep [Nat]
data St = St Nat [Step] Bool

-- | Existentially-wrapped premise action for runtime scheduling.
data PremAction rel = PremAction
  { paReq  :: Set Int  -- ^ Variables required (inputs)
  , paProd :: Set Int  -- ^ Variables produced (outputs)
  , paGoal :: rel ()   -- ^ Goal to execute
  }

-- | Negation action for negation-as-failure.
data NegAction rel = NegAction
  { naReq  :: Set Int  -- ^ Variables required (should be grounded before negation)
  , naGoal :: rel ()   -- ^ Goal to negate (succeeds if this fails)
  }

-- | An action to execute after concl (prem, neg, or lifted rel)
data DeferredAction rel
  = PremA (PremAction rel)
  | NegA (NegAction rel)
  | LiftedA (rel ())

-- | Conclusion action for runtime scheduling.
data ConclAction rel ts = ConclAction
  { caReq     :: Set Int           -- ^ Variables required from inputs
  , caPattern :: LTermList rel ts  -- ^ Pattern to unify with caller args
  }

-- | Collected rule state (used during rule construction).
data RuleState rel ts = RuleState
  { rsNextVar :: Int                      -- ^ Next fresh variable ID
  , rsConcl   :: Maybe (ConclAction rel ts)  -- ^ The conclusion (if declared)
  , rsPrems   :: [PremAction rel]            -- ^ Premises in declaration order
  }

-- | Initial empty rule state.
initRuleState :: RuleState rel ts
initRuleState = RuleState 0 Nothing []

-- | Rule monad with hybrid execution: concl is immediate, others collected.
-- 'ts' is the type list of the enclosing judgment.
--
-- The monad carries: caller's args (for concl) and collected deferred actions
data RuleEnv rel ts = RuleEnv
  { reArgs      :: LTermList rel ts       -- ^ Caller's arguments
  , reDeferred  :: [DeferredAction rel]   -- ^ Collected actions (reversed order)
  , reAvailVars :: Set Int                -- ^ Variables available after concl
  , reNextVar   :: Int                    -- ^ Next fresh variable ID (runtime counter)
  }

newtype RuleM (rel :: Type -> Type) (ts :: [Type]) (s :: St) (t :: St) a = RuleM
  { runRuleM :: RuleEnv rel ts -> rel (a, RuleEnv rel ts) }

return :: Redex rel => a -> RuleM rel ts s s a
return a = RuleM $ \env -> pure (a, env)

(>>=) :: Redex rel => RuleM rel ts s t a -> (a -> RuleM rel ts t u b) -> RuleM rel ts s u b
RuleM m >>= f = RuleM $ \env -> m env Prelude.>>= \(a, env') -> runRuleM (f a) env'

(>>) :: Redex rel => RuleM rel ts s t a -> RuleM rel ts t u b -> RuleM rel ts s u b
m >> k = m >>= \_ -> k

--------------------------------------------------------------------------------
-- Fresh
--------------------------------------------------------------------------------

-- | Create a fresh logic variable with runtime ID tracking.
fresh :: forall a rel ts n steps c.
         (Redex rel, LogicType a)
      => RuleM rel ts ('St n steps c) ('St (n + 1) steps c) (T '[n] a rel)
fresh = RuleM $ \env -> fresh_ FreshVar $ \lterm ->
  let varId = reNextVar env
  in pure (T (S.singleton varId) (Free lterm), env { reNextVar = varId + 1 })

-- | Create 2 fresh logic variables.
fresh2 :: forall a b rel ts n steps c.
          (Redex rel, LogicType a, LogicType b)
       => RuleM rel ts ('St n steps c) ('St (n + 2) steps c)
            (T '[n] a rel, T '[n + 1] b rel)
fresh2 = RuleM $ \env -> do
  (ta, env1) <- runRuleM (fresh @a) env
  (tb, env2) <- runRuleM (fresh @b) env1
  pure ((ta, tb), env2)

-- | Create 3 fresh logic variables.
fresh3 :: forall a b c rel ts n steps cc.
          (Redex rel, LogicType a, LogicType b, LogicType c)
       => RuleM rel ts ('St n steps cc) ('St (n + 3) steps cc)
            (T '[n] a rel, T '[n + 1] b rel, T '[n + 2] c rel)
fresh3 = RuleM $ \env -> do
  (ta, env1) <- runRuleM (fresh @a) env
  (tb, env2) <- runRuleM (fresh @b) env1
  (tc, env3) <- runRuleM (fresh @c) env2
  pure ((ta, tb, tc), env3)

-- | Create 4 fresh logic variables.
fresh4 :: forall a b c d rel ts n steps cc.
          (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d)
       => RuleM rel ts ('St n steps cc) ('St (n + 4) steps cc)
            (T '[n] a rel, T '[n + 1] b rel, T '[n + 2] c rel, T '[n + 3] d rel)
fresh4 = RuleM $ \env -> do
  (ta, env1) <- runRuleM (fresh @a) env
  (tb, env2) <- runRuleM (fresh @b) env1
  (tc, env3) <- runRuleM (fresh @c) env2
  (td, env4) <- runRuleM (fresh @d) env3
  pure ((ta, tb, tc, td), env4)

-- | Create 5 fresh logic variables.
fresh5 :: forall a b c d e rel ts n steps cc.
          (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d, LogicType e)
       => RuleM rel ts ('St n steps cc) ('St (n + 5) steps cc)
            (T '[n] a rel, T '[n + 1] b rel, T '[n + 2] c rel, T '[n + 3] d rel, T '[n + 4] e rel)
fresh5 = RuleM $ \env -> do
  (ta, env1) <- runRuleM (fresh @a) env
  (tb, env2) <- runRuleM (fresh @b) env1
  (tc, env3) <- runRuleM (fresh @c) env2
  (td, env4) <- runRuleM (fresh @d) env3
  (te, env5) <- runRuleM (fresh @e) env4
  pure ((ta, tb, tc, td, te), env5)

-- | Create 6 fresh logic variables.
fresh6 :: forall a b c d e f rel ts n steps cc.
          (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d, LogicType e, LogicType f)
       => RuleM rel ts ('St n steps cc) ('St (n + 6) steps cc)
            (T '[n] a rel, T '[n + 1] b rel, T '[n + 2] c rel, T '[n + 3] d rel, T '[n + 4] e rel, T '[n + 5] f rel)
fresh6 = RuleM $ \env -> do
  (ta, env1) <- runRuleM (fresh @a) env
  (tb, env2) <- runRuleM (fresh @b) env1
  (tc, env3) <- runRuleM (fresh @c) env2
  (td, env4) <- runRuleM (fresh @d) env3
  (te, env5) <- runRuleM (fresh @e) env4
  (tf, env6) <- runRuleM (fresh @f) env5
  pure ((ta, tb, tc, td, te, tf), env6)

--------------------------------------------------------------------------------
-- Lifting rel actions
--------------------------------------------------------------------------------

-- | Lift an arbitrary 'rel' action into 'RuleM' (immediate execution).
--
-- Use this for operations that produce a value needed in subsequent patterns,
-- such as generating fresh nominal atoms.
--
-- @
-- -- Generate a fresh nominal atom (no mode tracking, immediate)
-- x <- liftRel freshNom
-- @
liftRel :: Redex rel => rel a -> RuleM rel ts s s a
liftRel action = RuleM $ \env -> action Prelude.>>= \a -> pure (a, env)

-- | Lift a 'rel ()' action to be executed after premises (deferred).
--
-- Use this for inline operations that depend on variables bound by premises.
-- These actions will be executed after all @concl@ and @prem@ operations.
--
-- @
-- -- Execute instantiateTo after the premise binds tyBnd
-- liftRelDeferred $ instantiateTo tyBnd tyArg result
-- @
liftRelDeferred :: Redex rel => rel () -> RuleM rel ts s s ()
liftRelDeferred action = RuleM $ \env -> pure
  ( ()
  , env { reDeferred = LiftedA action : reDeferred env }
  )

--------------------------------------------------------------------------------
-- Moded Judgments
--------------------------------------------------------------------------------

-- | Result of applying a moded judgment. Carries mode info at type and runtime level.
data AppliedM rel (name :: Symbol) (modes :: [Mode]) (vss :: [[Nat]]) (ts :: [Type]) = AppliedM
  { amGoal    :: rel ()           -- ^ Goal to execute
  , amName    :: String           -- ^ Judgment name
  , amArgs    :: LTermList rel ts -- ^ Arguments (stripped of var tracking)
  , amReqVars :: Set Int          -- ^ Runtime: variables required (inputs)
  , amProdVars :: Set Int         -- ^ Runtime: variables produced (outputs)
  }

-- | Type alias for a unary moded judgment function.
--
-- Useful for readable signatures in examples (avoids spelling out @AppliedM@
-- indices like @vss@ and @ts@).
type Judgment1 rel (name :: Symbol) (modes :: [Mode]) (t1 :: Type) =
  forall vs1.
    ( InputVars modes '[vs1] '[t1]
    , OutputVars modes '[vs1] '[t1]
    ) =>
    T vs1 t1 rel -> AppliedM rel name modes '[vs1] '[t1]

-- | Type alias for a binary moded judgment function.
type Judgment2 rel (name :: Symbol) (modes :: [Mode]) (t1 :: Type) (t2 :: Type) =
  forall vs1 vs2.
    ( InputVars modes '[vs1, vs2] '[t1, t2]
    , OutputVars modes '[vs1, vs2] '[t1, t2]
    ) =>
    T vs1 t1 rel -> T vs2 t2 rel -> AppliedM rel name modes '[vs1, vs2] '[t1, t2]

-- | Type alias for a ternary moded judgment function.
type Judgment3 rel (name :: Symbol) (modes :: [Mode]) (t1 :: Type) (t2 :: Type) (t3 :: Type) =
  forall vs1 vs2 vs3.
    ( InputVars modes '[vs1, vs2, vs3] '[t1, t2, t3]
    , OutputVars modes '[vs1, vs2, vs3] '[t1, t2, t3]
    ) =>
    T vs1 t1 rel -> T vs2 t2 rel -> T vs3 t3 rel ->
    AppliedM rel name modes '[vs1, vs2, vs3] '[t1, t2, t3]

-- | Type alias for a quaternary moded judgment function.
type Judgment4 rel (name :: Symbol) (modes :: [Mode]) (t1 :: Type) (t2 :: Type) (t3 :: Type) (t4 :: Type) =
  forall vs1 vs2 vs3 vs4.
    ( InputVars modes '[vs1, vs2, vs3, vs4] '[t1, t2, t3, t4]
    , OutputVars modes '[vs1, vs2, vs3, vs4] '[t1, t2, t3, t4]
    ) =>
    T vs1 t1 rel -> T vs2 t2 rel -> T vs3 t3 rel -> T vs4 t4 rel ->
    AppliedM rel name modes '[vs1, vs2, vs3, vs4] '[t1, t2, t3, t4]

-- | Convert TArgs to LTermList (strip variable tracking).
class ToLTermList (vss :: [[Nat]]) (ts :: [Type]) where
  toLTermList :: TArgs vss ts rel -> LTermList rel ts

instance ToLTermList '[] '[] where
  toLTermList ANil = TNil

instance (LogicType t, ToLTermList vss ts) => ToLTermList (vs ': vss) (t ': ts) where
  toLTermList (t :! xs) = tTerm t :> toLTermList xs

-- | A moded judgment definition.
data MJudgeDef rel (name :: Symbol) (modes :: [Mode]) (ts :: [Type]) = MJudgeDef
  { mjdName  :: String
  , mjdRules :: [ModedRule rel ts]
  }

-- | Define a moded judgment. Returns a function that takes TArgs.
mjudge :: forall name modes rel ts vss.
          (Redex rel, KnownSymbol name, InputVars modes vss ts, OutputVars modes vss ts, ToLTermList vss ts)
       => ModeList modes
       -> [ModedRule rel ts]
       -> TArgs vss ts rel
       -> AppliedM rel name modes vss ts
mjudge modes rules args = AppliedM
  { amGoal = asum [ call $ Relation name (captureArgs (toLTermList args)) (body args)
                  | ModedRule name body <- rules
                  ]
  , amName = symbolVal (Proxy @name)
  , amArgs = toLTermList args
  , amReqVars = inputVars modes args
  , amProdVars = outputVars modes args
  }

-- | Define a unary moded judgment with curried syntax.
mjudge1 :: forall name modes rel t1.
           (Redex rel, KnownSymbol name, LogicType t1)
        => ModeList modes
        -> [ModedRule rel '[t1]]
        -> (forall vs1. (InputVars modes '[vs1] '[t1], OutputVars modes '[vs1] '[t1])
            => T vs1 t1 rel -> AppliedM rel name modes '[vs1] '[t1])
mjudge1 modes rules t1@(T vars1 _) =
  let args = t1 :! ANil
  in mjudge modes rules args

-- | Define a binary moded judgment with curried syntax.
mjudge2 :: forall name modes rel t1 t2.
           (Redex rel, KnownSymbol name, LogicType t1, LogicType t2)
        => ModeList modes
        -> [ModedRule rel '[t1, t2]]
        -> (forall vs1 vs2. (InputVars modes '[vs1, vs2] '[t1, t2], OutputVars modes '[vs1, vs2] '[t1, t2])
            => T vs1 t1 rel -> T vs2 t2 rel
            -> AppliedM rel name modes '[vs1, vs2] '[t1, t2])
mjudge2 modes rules t1@(T _ _) t2@(T _ _) =
  let args = t1 :! t2 :! ANil
  in mjudge modes rules args

-- | Define a ternary moded judgment with curried syntax.
mjudge3 :: forall name modes rel t1 t2 t3.
           (Redex rel, KnownSymbol name, LogicType t1, LogicType t2, LogicType t3)
        => ModeList modes
        -> [ModedRule rel '[t1, t2, t3]]
        -> (forall vs1 vs2 vs3. (InputVars modes '[vs1, vs2, vs3] '[t1, t2, t3], OutputVars modes '[vs1, vs2, vs3] '[t1, t2, t3])
            => T vs1 t1 rel -> T vs2 t2 rel -> T vs3 t3 rel
            -> AppliedM rel name modes '[vs1, vs2, vs3] '[t1, t2, t3])
mjudge3 modes rules t1@(T _ _) t2@(T _ _) t3@(T _ _) =
  let args = t1 :! t2 :! t3 :! ANil
  in mjudge modes rules args

-- | Convenience for 4-argument judgments.
mjudge4 :: forall name modes rel t1 t2 t3 t4.
           (Redex rel, KnownSymbol name, LogicType t1, LogicType t2, LogicType t3, LogicType t4)
        => ModeList modes
        -> [ModedRule rel '[t1, t2, t3, t4]]
        -> (forall vs1 vs2 vs3 vs4. (InputVars modes '[vs1, vs2, vs3, vs4] '[t1, t2, t3, t4], OutputVars modes '[vs1, vs2, vs3, vs4] '[t1, t2, t3, t4])
            => T vs1 t1 rel -> T vs2 t2 rel -> T vs3 t3 rel -> T vs4 t4 rel
            -> AppliedM rel name modes '[vs1, vs2, vs3, vs4] '[t1, t2, t3, t4])
mjudge4 modes rules t1@(T _ _) t2@(T _ _) t3@(T _ _) t4@(T _ _) =
  let args = t1 :! t2 :! t3 :! t4 :! ANil
  in mjudge modes rules args

-- | Define a unary moded judgment with scoped rule builder.
-- The judgment name and modes are specified via type application.
--
-- @
-- value = defJudge1 \@\"value\" \@'[I] $ \\rule ->
--   [ rule \"value-lam\" $ do
--       b <- fresh
--       concl $ value (lam b)
--   , rule \"value-zero\" $ do
--       concl $ value zero
--   ]
-- @
defJudge1 :: forall name modes rel t1.
             (RedexNeg rel, KnownSymbol name, LogicType t1, UnifyLList rel '[t1], SingModeList modes)
          => ((forall n steps. CheckSchedule name steps
               => String -> RuleM rel '[t1] ('St 0 '[] 'False) ('St n steps 'True) ()
               -> ModedRule rel '[t1])
              -> [ModedRule rel '[t1]])
          -> (forall vs1. (InputVars modes '[vs1] '[t1], OutputVars modes '[vs1] '[t1])
              => T vs1 t1 rel -> AppliedM rel name modes '[vs1] '[t1])
defJudge1 mkRules = mjudge1 singModeList (mkRules rule)
  where
    rule :: forall n steps. CheckSchedule name steps
         => String -> RuleM rel '[t1] ('St 0 '[] 'False) ('St n steps 'True) ()
         -> ModedRule rel '[t1]
    rule = ruleM @name

-- | Define a binary moded judgment with scoped rule builder.
defJudge2 :: forall name modes rel t1 t2.
             (RedexNeg rel, KnownSymbol name, LogicType t1, LogicType t2, UnifyLList rel '[t1, t2], SingModeList modes)
          => ((forall n steps. CheckSchedule name steps
               => String -> RuleM rel '[t1, t2] ('St 0 '[] 'False) ('St n steps 'True) ()
               -> ModedRule rel '[t1, t2])
              -> [ModedRule rel '[t1, t2]])
          -> (forall vs1 vs2. (InputVars modes '[vs1, vs2] '[t1, t2], OutputVars modes '[vs1, vs2] '[t1, t2])
              => T vs1 t1 rel -> T vs2 t2 rel
              -> AppliedM rel name modes '[vs1, vs2] '[t1, t2])
defJudge2 mkRules = mjudge2 singModeList (mkRules rule)
  where
    rule :: forall n steps. CheckSchedule name steps
         => String -> RuleM rel '[t1, t2] ('St 0 '[] 'False) ('St n steps 'True) ()
         -> ModedRule rel '[t1, t2]
    rule = ruleM @name

-- | Define a ternary moded judgment with scoped rule builder.
--
-- @
-- typeof = defJudge3 \@\"typeof\" \@'[I, I, O] $ \\rule ->
--   [ rule \"typeof-unit\" $ do
--       ctx <- fresh
--       concl $ typeof ctx unit tunit
--   , rule \"typeof-var\" $ do
--       (ctx, x, ty) <- fresh3
--       concl $ typeof ctx (var x) ty
--       prem $ lookupTm ctx x ty
--   ]
-- @
defJudge3 :: forall name modes rel t1 t2 t3.
             (RedexNeg rel, KnownSymbol name, LogicType t1, LogicType t2, LogicType t3, UnifyLList rel '[t1, t2, t3], SingModeList modes)
          => ((forall n steps. CheckSchedule name steps
               => String -> RuleM rel '[t1, t2, t3] ('St 0 '[] 'False) ('St n steps 'True) ()
               -> ModedRule rel '[t1, t2, t3])
              -> [ModedRule rel '[t1, t2, t3]])
          -> (forall vs1 vs2 vs3. (InputVars modes '[vs1, vs2, vs3] '[t1, t2, t3], OutputVars modes '[vs1, vs2, vs3] '[t1, t2, t3])
              => T vs1 t1 rel -> T vs2 t2 rel -> T vs3 t3 rel
              -> AppliedM rel name modes '[vs1, vs2, vs3] '[t1, t2, t3])
defJudge3 mkRules = mjudge3 singModeList (mkRules rule)
  where
    rule :: forall n steps. CheckSchedule name steps
         => String -> RuleM rel '[t1, t2, t3] ('St 0 '[] 'False) ('St n steps 'True) ()
         -> ModedRule rel '[t1, t2, t3]
    rule = ruleM @name

-- | Define a quaternary moded judgment with scoped rule builder.
defJudge4 :: forall name modes rel t1 t2 t3 t4.
             (RedexNeg rel, KnownSymbol name, LogicType t1, LogicType t2, LogicType t3, LogicType t4, UnifyLList rel '[t1, t2, t3, t4], SingModeList modes)
          => ((forall n steps. CheckSchedule name steps
               => String -> RuleM rel '[t1, t2, t3, t4] ('St 0 '[] 'False) ('St n steps 'True) ()
               -> ModedRule rel '[t1, t2, t3, t4])
              -> [ModedRule rel '[t1, t2, t3, t4]])
          -> (forall vs1 vs2 vs3 vs4. (InputVars modes '[vs1, vs2, vs3, vs4] '[t1, t2, t3, t4], OutputVars modes '[vs1, vs2, vs3, vs4] '[t1, t2, t3, t4])
              => T vs1 t1 rel -> T vs2 t2 rel -> T vs3 t3 rel -> T vs4 t4 rel
              -> AppliedM rel name modes '[vs1, vs2, vs3, vs4] '[t1, t2, t3, t4])
defJudge4 mkRules = mjudge4 singModeList (mkRules rule)
  where
    rule :: forall n steps. CheckSchedule name steps
         => String -> RuleM rel '[t1, t2, t3, t4] ('St 0 '[] 'False) ('St n steps 'True) ()
         -> ModedRule rel '[t1, t2, t3, t4]
    rule = ruleM @name

-- | Convert AppliedM to Applied for running queries.
toApplied :: AppliedM rel name modes vss ts -> Applied rel ts
toApplied (AppliedM goal name args _ _) = Applied args goal name

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

-- | Declare conclusion. Executes immediately: unifies pattern with caller's arguments.
-- Also stores the input vars as available for scheduling premises.
concl :: forall name modes rel vss ts n steps.
         (Redex rel, UnifyLList rel ts)
      => AppliedM rel name modes vss ts
      -> RuleM rel ts ('St n steps 'False)
                   ('St n (Snoc steps ('ConcStep name (ReqVars modes vss))) 'True) ()
concl applied = RuleM $ \env -> do
  markConclusion
  unifyLList (amArgs applied) (reArgs env)
  pure ((), env { reAvailVars = amReqVars applied })

captureArgs :: LTermList rel ts -> [CapturedTerm rel]
captureArgs TNil = []
captureArgs (x :> xs) = CapturedTerm x : captureArgs xs

-- | Declare premise. Collects for later execution.
-- The premise will be executed after the conclusion, in declaration order.
prem :: forall name modes rel vss ts ts' n steps c.
        Redex rel
     => AppliedM rel name modes vss ts'
     -> RuleM rel ts ('St n steps c)
                  ('St n (Snoc steps ('PremStep ('Goal name (ReqVars modes vss) (ProdVars modes vss)))) c) ()
prem applied = RuleM $ \env -> do
  markPremise (amName applied) (captureArgs (amArgs applied))
  pure
    ( ()
    , env { reDeferred = PremA (PremAction (amReqVars applied) (amProdVars applied) (amGoal applied)) : reDeferred env }
    )

-- | Declare negation-as-failure. The goal must fail for the rule to succeed.
--
-- Negations are statically checked: ALL variables (both input and output
-- positions) must be grounded before the negation can execute. This is
-- because negation-as-failure checks whether the goal has any solutions,
-- which requires all variables to have known values.
--
-- @
-- -- "x is not in the context" can be expressed as:
-- neg $ lookupCtx ctx x ty  -- requires ctx, x, AND ty to be grounded
-- @
neg :: forall name modes rel vss ts ts' n steps c.
       Redex rel
    => AppliedM rel name modes vss ts'
    -> RuleM rel ts ('St n steps c)
                 ('St n (Snoc steps ('NegStep (AllVars modes vss))) c) ()
neg applied = RuleM $ \env -> pure
  ( ()
  , env { reDeferred = NegA (NegAction (S.union (amReqVars applied) (amProdVars applied)) (amGoal applied)) : reDeferred env }
  )

-- | Unify two argument lists.
class UnifyTArgs rel ts where
  unifyTArgs :: TArgs vss1 ts rel -> TArgs vss2 ts rel -> rel ()

instance Redex rel => UnifyTArgs rel '[] where
  unifyTArgs ANil ANil = pure ()

instance (LogicType t, Redex rel, UnifyTArgs rel ts) => UnifyTArgs rel (t ': ts) where
  unifyTArgs (T _ x :! xs) (T _ y :! ys) = (x <=> y) Prelude.>> unifyTArgs xs ys

--------------------------------------------------------------------------------
-- Schedule Checking
--------------------------------------------------------------------------------

type family ConclVars (steps :: [Step]) :: [Nat] where
  ConclVars ('ConcStep _ vs ': _) = vs
  ConclVars (_ ': rest) = ConclVars rest
  ConclVars '[] = TypeError ('Text "Rule is missing a conclusion (concl)")

type family PremGoals (steps :: [Step]) :: [Goal] where
  PremGoals '[] = '[]
  PremGoals ('PremStep g ': rest) = g ': PremGoals rest
  PremGoals ('ConcStep _ _ ': rest) = PremGoals rest
  PremGoals ('NegStep _ ': rest) = PremGoals rest

-- | Extract negation requirements from steps.
type family NegReqs (steps :: [Step]) :: [[Nat]] where
  NegReqs '[] = '[]
  NegReqs ('NegStep req ': rest) = req ': NegReqs rest
  NegReqs ('PremStep _ ': rest) = NegReqs rest
  NegReqs ('ConcStep _ _ ': rest) = NegReqs rest

-- | Compute all variables produced by premises.
type family AllPremProds (gs :: [Goal]) :: [Nat] where
  AllPremProds '[] = '[]
  AllPremProds ('Goal _ _ prod ': rest) = Union prod (AllPremProds rest)

-- | Compute final available variables (concl inputs + all prem outputs).
type family FinalAvail (steps :: [Step]) :: [Nat] where
  FinalAvail steps = Union (ConclVars steps) (AllPremProds (PremGoals steps))

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
  CheckSchedule name steps =
    ( CheckPremises name steps (Solve (ConclVars steps) (PremGoals steps))
    , CheckNegations name steps (FinalAvail steps) (NegReqs steps)
    )

-- | Check that all premises can be scheduled.
type family CheckPremises (name :: Symbol) (steps :: [Step]) (r :: SolveResult) :: Constraint where
  CheckPremises _ _ 'Solved = ()
  CheckPremises name steps ('Stuck avail gs) = TypeError
    ( 'Text "In rule \"" ':<>: 'Text name ':<>: 'Text "\": cannot schedule premises"
        ':$$: 'Text ""
        ':$$: 'Text "  Grounded variables: " ':<>: 'ShowType avail
        ':$$: 'Text "  Blocked premises:"
        ':$$: ShowBlocked avail gs
        ':$$: 'Text ""
        ':$$: 'Text "  (Variable indices are assigned by fresh in declaration order: 0, 1, 2, ...)"
        ':$$: 'Text ""
        ':$$: 'Text "  To fix: ensure each premise's input variables are grounded"
        ':$$: 'Text "          by the conclusion or a prior premise's outputs."
    )

-- | Check that all negations have their inputs grounded.
type family CheckNegations (name :: Symbol) (steps :: [Step]) (avail :: [Nat]) (negs :: [[Nat]]) :: Constraint where
  CheckNegations _ _ _ '[] = ()
  CheckNegations name steps avail (req ': rest) =
    If (Subset req avail)
       (CheckNegations name steps avail rest)
       (TypeError
         ( 'Text "In rule \"" ':<>: 'Text name ':<>: 'Text "\": negation uses ungrounded variables"
             ':$$: 'Text ""
             ':$$: 'Text "  Grounded (from conclusion + premises): " ':<>: 'ShowType avail
             ':$$: 'Text "  Negation requires:                     " ':<>: 'ShowType req
             ':$$: 'Text "  Ungrounded:                            " ':<>: 'ShowType (Diff req avail)
             ':$$: 'Text ""
             ':$$: 'Text "  (Variable indices are assigned by fresh in declaration order: 0, 1, 2, ...)"
             ':$$: 'Text ""
             ':$$: 'Text "  To fix: ensure ungrounded variables appear in conclusion inputs"
             ':$$: 'Text "          or are produced by a premise before the negation."
         ))

type family ShowBlocked (avail :: [Nat]) (gs :: [Goal]) :: ErrorMessage where
  ShowBlocked _ '[] = 'Text ""
  ShowBlocked avail ('Goal name req _ ': rest) =
    ('Text "    - " ':<>: 'Text name ':<>: 'Text ": needs " ':<>: 'ShowType (Diff req avail) ':<>: 'Text " (inputs: " ':<>: 'ShowType req ':<>: 'Text ")")
      ':$$: ShowBlocked avail rest

--------------------------------------------------------------------------------
-- Moded Rules (with Runtime Scheduling)
--------------------------------------------------------------------------------

-- | A moded rule.
data ModedRule rel (ts :: [Type]) = ModedRule
  { mrName :: String
  , mrBody :: forall vss. ToLTermList vss ts => TArgs vss ts rel -> rel ()
  }

-- | Schedule premises based on data dependencies.
--
-- Starting with available variables from the conclusion's inputs,
-- repeatedly select a premise whose required vars are all available,
-- execute it, and add its produced vars to the available set.
--
-- Since 'CheckSchedule' guarantees a valid schedule exists at compile time,
-- this runtime scheduling will always succeed.
schedulePremises :: Redex rel => Set Int -> [PremAction rel] -> rel ()
schedulePremises _ [] = pure ()
schedulePremises avail prems =
  case selectReady avail prems of
    Just (ready, rest) -> do
      paGoal ready
      schedulePremises (S.union avail (paProd ready)) rest
    Nothing ->
      -- This should never happen if CheckSchedule passed
      error "Runtime scheduling failed: no ready premises (should be impossible)"

-- | Select a premise whose required vars are all available.
selectReady :: Set Int -> [PremAction rel] -> Maybe (PremAction rel, [PremAction rel])
selectReady _ [] = Nothing
selectReady avail (p:ps)
  | paReq p `S.isSubsetOf` avail = Just (p, ps)
  | otherwise = case selectReady avail ps of
      Nothing -> Nothing
      Just (ready, rest) -> Just (ready, p : rest)

-- | Create a moded rule with hybrid execution and runtime scheduling.
--
-- - The @concl@ declaration executes immediately (required for nominal logic)
-- - The @prem@ declarations are scheduled based on data dependencies
-- - The @neg@ declarations execute after premises (statically verified safe)
-- - The @liftRelDeferred@ declarations execute after all premises and negations
--
-- This approach allows @prem@ declarations to appear in any order—the
-- runtime scheduler reorders them based on which variables are available.
ruleM :: forall name rel n steps ts.
         (RedexNeg rel, CheckSchedule name steps, UnifyLList rel ts)
      => String
      -> RuleM rel ts ('St 0 '[] 'False) ('St n steps 'True) ()
      -> ModedRule rel ts
ruleM name body = ModedRule name $ \args -> do
  let initEnv = RuleEnv (toLTermList args) [] S.empty 0
  -- Run the body: concl executes immediately, prems/negs/lifted are collected
  ((), finalEnv) <- runRuleM body initEnv
  -- Separate deferred actions into premises, negations, and lifted
  let deferred = reverse (reDeferred finalEnv)  -- source order
      (prems, negs, lifted) = partitionDeferred deferred
  -- Schedule premises based on data dependencies
  schedulePremises (reAvailVars finalEnv) prems
  -- Execute negations (statically verified to have all inputs grounded)
  executeNegations negs
  -- Execute lifted actions in source order after all premises and negations
  -- (unless the interpreter is a rule extractor that wants to skip them)
  if skipLiftedActions (Proxy :: Proxy rel) then pure () else executeLifted lifted

-- | Partition deferred actions into premises, negations, and lifted actions.
partitionDeferred :: [DeferredAction rel] -> ([PremAction rel], [NegAction rel], [rel ()])
partitionDeferred = foldr go ([], [], [])
  where
    go (PremA p)   (ps, ns, ls) = (p:ps, ns, ls)
    go (NegA n)    (ps, ns, ls) = (ps, n:ns, ls)
    go (LiftedA l) (ps, ns, ls) = (ps, ns, l:ls)

-- | Execute negations in source order.
-- Since CheckSchedule guarantees all negation inputs are grounded,
-- no runtime scheduling is needed.
executeNegations :: RedexNeg rel => [NegAction rel] -> rel ()
executeNegations [] = pure ()
executeNegations (n:ns) = R.neg (naGoal n) Prelude.>> executeNegations ns

-- | Execute lifted actions in order.
executeLifted :: Redex rel => [rel ()] -> rel ()
executeLifted [] = pure ()
executeLifted (a:as) = a Prelude.>> executeLifted as
