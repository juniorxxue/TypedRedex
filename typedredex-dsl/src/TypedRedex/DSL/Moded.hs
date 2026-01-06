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
  , lift1, lift2, lift3, lift4
    -- * Argument lists
  , TArgs(..)
    -- * Moded judgments
  , AppliedM(..)
  , Judgment1
  , Judgment2
  , Judgment3
  , Judgment4
  , Judgment5
  , Judgment6
    -- ** Moded judgment aliases (In/Out syntax)
  , In, Out, GetMode, GetType
  , MJudgment1, MJudgment2, MJudgment3, MJudgment4, MJudgment5, MJudgment6
  , mjudge, mjudge1, mjudge2, mjudge3, mjudge4, mjudge5, mjudge6
  , defJudge1, defJudge2, defJudge3, defJudge4, defJudge5, defJudge6
  , toApplied
  , ToLTermList(..)
    -- * Rule building
  , RuleM
  , ruleM
  , ModedRule(..)
    -- * Rule operations
  , Fresh(..)
  , prem
  , neg
  , (===), (=/=)
  , concl
  , liftRel
  , liftRelDeferred
  , unbind2M
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
import GHC.TypeNats (Nat, type (+), CmpNat)
import Data.Proxy (Proxy(..))
import Control.Applicative (asum)
import qualified Data.Set as S
import Data.Set (Set)

import GHC.Generics (Generic, Rep, to, K1(..), M1(..), U1(..), (:*:)(..), (:+:))

import TypedRedex.Logic (Redex(..), Relation(..), CapturedTerm(..), FreshType(..), RedexNeg, Logic(..), LogicType(..), RedexEval, HasDisplay)
import qualified TypedRedex.Logic as R (neg)
import TypedRedex.DSL.Fresh (LTerm)
import TypedRedex.DSL.Define (Applied(..), LTermList(..))
import TypedRedex.DSL.Relation (call, (<=>))
import TypedRedex.Nominal.Bind (Bind, Permute(..), mkBindL)
import TypedRedex.Nominal.Prelude (FreshName(..), unbind2)
import TypedRedex.Logic.Redex (RedexFresh)
import Data.Typeable (Typeable)

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
-- Moded Type Wrappers
--------------------------------------------------------------------------------

-- | Phantom type wrapper for input mode with associated type.
-- Used for concise judgment signatures: @MJudgment2 rel "foo" (In Env) (Out Ty)@
data In (a :: Type)

-- | Phantom type wrapper for output mode with associated type.
data Out (a :: Type)

-- | Extract mode from a moded type wrapper.
type family GetMode (x :: Type) :: Mode where
  GetMode (In _)  = 'I
  GetMode (Out _) = 'O

-- | Extract the underlying type from a moded type wrapper.
type family GetType (x :: Type) :: Type where
  GetType (In a)  = a
  GetType (Out a) = a

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

-- | Lift a quaternary function, merging variable sets.
lift4 :: (LTerm a rel -> LTerm b rel -> LTerm c rel -> LTerm d rel -> LTerm e rel)
      -> T vs1 a rel -> T vs2 b rel -> T vs3 c rel -> T vs4 d rel
      -> T (Union vs1 (Union vs2 (Union vs3 vs4))) e rel
lift4 f (T vars1 x) (T vars2 y) (T vars3 z) (T vars4 w) = T (S.unions [vars1, vars2, vars3, vars4]) (f x y z w)

--------------------------------------------------------------------------------
-- Type-level Sorted Sets (O(n) operations using CmpNat)
--------------------------------------------------------------------------------

type family If (b :: Bool) (t :: k) (f :: k) :: k where
  If 'True  t _ = t
  If 'False _ f = f

-- | Insert into sorted list, maintaining ascending order. O(n)
type family Insert (x :: Nat) (xs :: [Nat]) :: [Nat] where
  Insert x '[] = '[x]
  Insert x (y ': ys) = InsertCmp (CmpNat x y) x y ys

type family InsertCmp (o :: Ordering) (x :: Nat) (y :: Nat) (ys :: [Nat]) :: [Nat] where
  InsertCmp 'LT x y ys = x ': y ': ys       -- x < y: insert here
  InsertCmp 'EQ _ y ys = y ': ys            -- x == y: already present
  InsertCmp 'GT x y ys = y ': Insert x ys   -- x > y: keep looking

-- | Merge two sorted lists into sorted result. O(n + m)
type family Union (xs :: [Nat]) (ys :: [Nat]) :: [Nat] where
  Union '[] ys = ys
  Union xs '[] = xs
  Union (x ': xs) (y ': ys) = UnionCmp (CmpNat x y) x xs y ys

type family UnionCmp (o :: Ordering) (x :: Nat) (xs :: [Nat]) (y :: Nat) (ys :: [Nat]) :: [Nat] where
  UnionCmp 'LT x xs y ys = x ': Union xs (y ': ys)   -- x < y: take x
  UnionCmp 'EQ x xs _ ys = x ': Union xs ys          -- x == y: take one, skip both
  UnionCmp 'GT x xs y ys = y ': Union (x ': xs) ys   -- x > y: take y

-- | Check if first sorted list is subset of second. O(n + m)
type family Subset (xs :: [Nat]) (ys :: [Nat]) :: Bool where
  Subset '[] _ = 'True
  Subset (_ ': _) '[] = 'False
  Subset (x ': xs) (y ': ys) = SubsetCmp (CmpNat x y) x xs y ys

type family SubsetCmp (o :: Ordering) (x :: Nat) (xs :: [Nat]) (y :: Nat) (ys :: [Nat]) :: Bool where
  SubsetCmp 'LT _ _ _ _ = 'False                    -- x < y: x not in ys
  SubsetCmp 'EQ _ xs _ ys = Subset xs ys            -- x == y: found, continue
  SubsetCmp 'GT x xs _ ys = Subset (x ': xs) ys     -- x > y: skip y, keep looking

-- | Compute set difference (xs - ys) for sorted lists. O(n + m)
type family Diff (xs :: [Nat]) (ys :: [Nat]) :: [Nat] where
  Diff '[] _ = '[]
  Diff xs '[] = xs
  Diff (x ': xs) (y ': ys) = DiffCmp (CmpNat x y) x xs y ys

type family DiffCmp (o :: Ordering) (x :: Nat) (xs :: [Nat]) (y :: Nat) (ys :: [Nat]) :: [Nat] where
  DiffCmp 'LT x xs y ys = x ': Diff xs (y ': ys)   -- x < y: x not in ys, keep it
  DiffCmp 'EQ _ xs _ ys = Diff xs ys               -- x == y: x in ys, remove it
  DiffCmp 'GT x xs _ ys = Diff (x ': xs) ys        -- x > y: skip y

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
data Step = ConcStep Symbol [Nat] [Nat]  -- ^ name, input vars, output vars
          | PremStep Goal
          | NegStep [Nat]
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

-- | Create a fresh logic variable with runtime ID tracking (single variable).
fresh1 :: forall a rel ts n steps c.
          (Redex rel, LogicType a)
       => RuleM rel ts ('St n steps c) ('St (n + 1) steps c) (T '[n] a rel)
fresh1 = RuleM $ \env -> fresh_ FreshVar $ \lterm ->
  let varId = reNextVar env
  in pure (T (S.singleton varId) (Free lterm), env { reNextVar = varId + 1 })

--------------------------------------------------------------------------------
-- Fresh typeclass (generic fresh for tuples)
--------------------------------------------------------------------------------

-- | Closed type family for counting fresh variables.
-- Single T values produce 1; tuples use GFreshCount via Generics.
type family FreshCount r :: Nat where
  FreshCount (T vs a rel) = 1
  FreshCount r = GFreshCount (Rep r)

-- | Typeclass for allocating fresh logic variables.
-- Works for single T values and tuples of T values.
class Fresh r rel ts n steps c where
  fresh :: RuleM rel ts ('St n steps c) ('St (n + FreshCount r) steps c) r

-- Base case: single variable (constrain vs ~ '[n] to force correct indices)
instance (Redex rel, LogicType a, vs ~ '[n]) => Fresh (T vs a rel) rel ts n steps c where
  fresh = fresh1 @a

-- Generic case: tuples and other product types
instance {-# OVERLAPPABLE #-}
  ( Redex rel, Generic r, GFresh (Rep r) rel ts n steps c
  , FreshCount r ~ GFreshCount (Rep r)
  ) => Fresh r rel ts n steps c where
  fresh = RuleM $ \env -> runRuleM (gfresh @(Rep r) @rel @ts @n @steps @c) env Prelude.>>= \(rep, env') ->
    Prelude.pure (to rep, env')

--------------------------------------------------------------------------------
-- GFresh (Generic traversal for fresh allocation)
--------------------------------------------------------------------------------

-- | Generic fresh variable allocation for product types
class GFresh f rel ts n steps c where
  type GFreshCount f :: Nat
  gfresh :: RuleM rel ts ('St n steps c) ('St (n + GFreshCount f) steps c) (f p)

-- Unit (empty product)
instance Redex rel => GFresh U1 rel ts n steps c where
  type GFreshCount U1 = 0
  gfresh = return U1

-- Metadata wrapper (pass through)
instance (Redex rel, GFresh f rel ts n steps c) => GFresh (M1 i m f) rel ts n steps c where
  type GFreshCount (M1 i m f) = GFreshCount f
  gfresh = liftGFresh M1 (gfresh @f @rel @ts @n @steps @c)

-- Product: process left then right, threading state
instance ( Redex rel
         , GFresh f rel ts n steps c
         , GFresh g rel ts (n + GFreshCount f) steps c
         ) => GFresh (f :*: g) rel ts n steps c where
  type GFreshCount (f :*: g) = GFreshCount f + GFreshCount g
  gfresh = RuleM $ \env -> do
    (a, env1) <- runRuleM (gfresh @f @rel @ts @n @steps @c) env
    (b, env2) <- runRuleM (gfresh @g @rel @ts @(n + GFreshCount f) @steps @c) env1
    Prelude.pure (a :*: b, env2)

-- Leaf: single T value (constrain vs ~ '[n] to force correct indices)
instance (Redex rel, LogicType a, vs ~ '[n]) => GFresh (K1 i (T vs a rel)) rel ts n steps c where
  type GFreshCount (K1 i (T vs a rel)) = 1
  gfresh = RuleM $ \env -> runRuleM (fresh1 @a) env Prelude.>>= \(t, env') ->
    Prelude.pure (K1 t, env')

-- Sum types: reject with TypeError
instance TypeError ('Text "Fresh does not support sum types (use product types like tuples)")
  => GFresh (f :+: g) rel ts n steps c where
  type GFreshCount (f :+: g) = 0
  gfresh = error "unreachable"

-- Helper for M1 lifting
liftGFresh :: Redex rel => (f p -> g p) -> RuleM rel ts s t (f p) -> RuleM rel ts s t (g p)
liftGFresh f m = RuleM $ \env -> runRuleM m env Prelude.>>= \(a, env') -> Prelude.pure (f a, env')

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

-- | Moded version of 'unbind2' for opening two binders with the same fresh name.
--
-- Participates in mode-based scheduling: the unbind operation is deferred
-- until the input binders become ground. This allows placing @unbind2M@
-- anywhere in the rule body.
--
-- Essential for rules comparing ∀-types (subtyping, equivalence)
-- where both bodies must refer to the same bound variable.
--
-- @
-- rule "forall" $ do
--     (env1, env2, p) <- fresh
--     (bd1, bd2) <- fresh
--     (a, tyA, tyB) <- unbind2M bd1 bd2  -- scheduled after concl grounds bd1, bd2
--     prem  $ ssub (euvar a env1) tyA p tyB (euvar a env2)
--     concl $ ssub env1 (tforall bd1) p (tforall bd2) env2
-- @
unbind2M ::
  forall name body1 body2 rel ts vs1 vs2 n steps c.
  ( Redex rel, RedexFresh rel, RedexEval rel
  , FreshName name, LogicType name
  , LogicType body1, LogicType body2
  , Permute name body1, Permute name body2
  , HasDisplay name, HasDisplay body1, HasDisplay body2
  ) =>
  T vs1 (Bind name body1) rel ->
  T vs2 (Bind name body2) rel ->
  RuleM rel ts ('St n steps c)
               ('St (n + 3) (Snoc steps ('PremStep ('Goal "unbind2" (Union vs1 vs2) '[n, n + 1, n + 2]))) c)
               (T '[n] name rel, T '[n + 1] body1 rel, T '[n + 2] body2 rel)
unbind2M (T vs1 bd1) (T vs2 bd2) = RuleM $ \env -> do
  let n = reNextVar env
      reqVars = S.union vs1 vs2
      prodVars = S.fromList [n, n + 1, n + 2]
  -- Allocate 3 fresh logic variables for the outputs
  fresh_ FreshVar $ \nameVar ->
    fresh_ FreshVar $ \bodyVar1 ->
      fresh_ FreshVar $ \bodyVar2 -> do
        let nameL  = Free nameVar
            body1L = Free bodyVar1
            body2L = Free bodyVar2
            -- The goal: open binders and unify with fresh vars
            goal
              | skipLiftedActions (Proxy :: Proxy rel) =
                  -- Typesetting mode: unify with synthetic binders to extract structure
                  unify bd1 (mkBindL nameL body1L) Prelude.>>
                  unify bd2 (mkBindL nameL body2L)
              | otherwise =
                  unbind2 bd1 bd2 Prelude.>>= \(name', body1', body2') ->
                    (nameL <=> name') Prelude.>>
                    (body1L <=> body1') Prelude.>>
                    (body2L <=> body2')
        markPremise "unbind2" [CapturedTerm bd1, CapturedTerm bd2] unbind2Fmt
        Prelude.pure
          ( ( T (S.singleton n) nameL
            , T (S.singleton (n + 1)) body1L
            , T (S.singleton (n + 2)) body2L )
          , env { reNextVar = n + 3
                , reDeferred = PremA (PremAction reqVars prodVars goal) : reDeferred env
                }
          )
  where
    unbind2Fmt [b1, b2] = "unbind2(" ++ b1 ++ ", " ++ b2 ++ ")"
    unbind2Fmt args = "unbind2(" ++ unwords args ++ ")"

--------------------------------------------------------------------------------
-- Moded Judgments
--------------------------------------------------------------------------------

-- | Result of applying a moded judgment. Carries mode info at type and runtime level.
data AppliedM rel (name :: Symbol) (modes :: [Mode]) (vss :: [[Nat]]) (ts :: [Type]) = AppliedM
  { amGoal     :: rel ()           -- ^ Goal to execute
  , amName     :: String           -- ^ Judgment name
  , amArgs     :: LTermList rel ts -- ^ Arguments (stripped of var tracking)
  , amReqVars  :: Set Int          -- ^ Runtime: variables required (inputs)
  , amProdVars :: Set Int          -- ^ Runtime: variables produced (outputs)
  , amFormat   :: [String] -> String -- ^ Format function for pretty printing
  }

-- | Type alias for a unary moded judgment function.
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

-- | Type alias for a 5-ary moded judgment function.
type Judgment5 rel (name :: Symbol) (modes :: [Mode]) (t1 :: Type) (t2 :: Type) (t3 :: Type) (t4 :: Type) (t5 :: Type) =
  forall vs1 vs2 vs3 vs4 vs5.
    ( InputVars modes '[vs1, vs2, vs3, vs4, vs5] '[t1, t2, t3, t4, t5]
    , OutputVars modes '[vs1, vs2, vs3, vs4, vs5] '[t1, t2, t3, t4, t5]
    ) =>
    T vs1 t1 rel -> T vs2 t2 rel -> T vs3 t3 rel -> T vs4 t4 rel -> T vs5 t5 rel ->
    AppliedM rel name modes '[vs1, vs2, vs3, vs4, vs5] '[t1, t2, t3, t4, t5]

-- | Type alias for a 6-ary moded judgment function.
type Judgment6 rel (name :: Symbol) (modes :: [Mode]) (t1 :: Type) (t2 :: Type) (t3 :: Type) (t4 :: Type) (t5 :: Type) (t6 :: Type) =
  forall vs1 vs2 vs3 vs4 vs5 vs6.
    ( InputVars modes '[vs1, vs2, vs3, vs4, vs5, vs6] '[t1, t2, t3, t4, t5, t6]
    , OutputVars modes '[vs1, vs2, vs3, vs4, vs5, vs6] '[t1, t2, t3, t4, t5, t6]
    ) =>
    T vs1 t1 rel -> T vs2 t2 rel -> T vs3 t3 rel -> T vs4 t4 rel -> T vs5 t5 rel -> T vs6 t6 rel ->
    AppliedM rel name modes '[vs1, vs2, vs3, vs4, vs5, vs6] '[t1, t2, t3, t4, t5, t6]

--------------------------------------------------------------------------------
-- Moded Judgment Aliases (using In/Out wrappers)
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

-- | Convert TArgs to LTermList (strip variable tracking).
class ToLTermList (vss :: [[Nat]]) (ts :: [Type]) where
  toLTermList :: TArgs vss ts rel -> LTermList rel ts

instance ToLTermList '[] '[] where
  toLTermList ANil = TNil

instance (LogicType t, ToLTermList vss ts) => ToLTermList (vs ': vss) (t ': ts) where
  toLTermList (t :! xs) = tTerm t :> toLTermList xs

-- | A moded judgment definition.
data MJudgeDef rel (name :: Symbol) (modes :: [Mode]) (ts :: [Type]) = MJudgeDef
  { mjdName   :: String
  , mjdFormat :: [String] -> String
  , mjdRules  :: [ModedRule rel ts]
  }

-- | Define a moded judgment. Returns a function that takes TArgs.
mjudge :: forall name modes rel ts vss.
          (Redex rel, KnownSymbol name, InputVars modes vss ts, OutputVars modes vss ts, ToLTermList vss ts)
       => ModeList modes
       -> ([String] -> String)  -- ^ Format function
       -> [ModedRule rel ts]
       -> TArgs vss ts rel
       -> AppliedM rel name modes vss ts
mjudge modes format rules args = AppliedM
  { amGoal = asum [ call $ Relation judgeName name (captureArgs (toLTermList args)) (body args) format
                  | ModedRule name body <- rules
                  ]
  , amName = judgeName
  , amArgs = toLTermList args
  , amReqVars = inputVars modes args
  , amProdVars = outputVars modes args
  , amFormat = format
  }
  where
    judgeName = symbolVal (Proxy @name)

mjudge1 :: forall name modes rel t1.
           (Redex rel, KnownSymbol name, LogicType t1)
        => ModeList modes
        -> ([String] -> String)
        -> [ModedRule rel '[t1]]
        -> (forall vs1. (InputVars modes '[vs1] '[t1], OutputVars modes '[vs1] '[t1])
            => T vs1 t1 rel -> AppliedM rel name modes '[vs1] '[t1])
mjudge1 modes format rules t1@(T vars1 _) =
  let args = t1 :! ANil
  in mjudge modes format rules args

mjudge2 :: forall name modes rel t1 t2.
           (Redex rel, KnownSymbol name, LogicType t1, LogicType t2)
        => ModeList modes
        -> ([String] -> String)
        -> [ModedRule rel '[t1, t2]]
        -> (forall vs1 vs2. (InputVars modes '[vs1, vs2] '[t1, t2], OutputVars modes '[vs1, vs2] '[t1, t2])
            => T vs1 t1 rel -> T vs2 t2 rel
            -> AppliedM rel name modes '[vs1, vs2] '[t1, t2])
mjudge2 modes format rules t1@(T _ _) t2@(T _ _) =
  let args = t1 :! t2 :! ANil
  in mjudge modes format rules args

mjudge3 :: forall name modes rel t1 t2 t3.
           (Redex rel, KnownSymbol name, LogicType t1, LogicType t2, LogicType t3)
        => ModeList modes
        -> ([String] -> String)
        -> [ModedRule rel '[t1, t2, t3]]
        -> (forall vs1 vs2 vs3. (InputVars modes '[vs1, vs2, vs3] '[t1, t2, t3], OutputVars modes '[vs1, vs2, vs3] '[t1, t2, t3])
            => T vs1 t1 rel -> T vs2 t2 rel -> T vs3 t3 rel
            -> AppliedM rel name modes '[vs1, vs2, vs3] '[t1, t2, t3])
mjudge3 modes format rules t1@(T _ _) t2@(T _ _) t3@(T _ _) =
  let args = t1 :! t2 :! t3 :! ANil
  in mjudge modes format rules args

mjudge4 :: forall name modes rel t1 t2 t3 t4.
           (Redex rel, KnownSymbol name, LogicType t1, LogicType t2, LogicType t3, LogicType t4)
        => ModeList modes
        -> ([String] -> String)
        -> [ModedRule rel '[t1, t2, t3, t4]]
        -> (forall vs1 vs2 vs3 vs4. (InputVars modes '[vs1, vs2, vs3, vs4] '[t1, t2, t3, t4], OutputVars modes '[vs1, vs2, vs3, vs4] '[t1, t2, t3, t4])
            => T vs1 t1 rel -> T vs2 t2 rel -> T vs3 t3 rel -> T vs4 t4 rel
            -> AppliedM rel name modes '[vs1, vs2, vs3, vs4] '[t1, t2, t3, t4])
mjudge4 modes format rules t1@(T _ _) t2@(T _ _) t3@(T _ _) t4@(T _ _) =
  let args = t1 :! t2 :! t3 :! t4 :! ANil
  in mjudge modes format rules args

mjudge5 :: forall name modes rel t1 t2 t3 t4 t5.
           (Redex rel, KnownSymbol name, LogicType t1, LogicType t2, LogicType t3, LogicType t4, LogicType t5)
        => ModeList modes
        -> ([String] -> String)
        -> [ModedRule rel '[t1, t2, t3, t4, t5]]
        -> (forall vs1 vs2 vs3 vs4 vs5. (InputVars modes '[vs1, vs2, vs3, vs4, vs5] '[t1, t2, t3, t4, t5], OutputVars modes '[vs1, vs2, vs3, vs4, vs5] '[t1, t2, t3, t4, t5])
            => T vs1 t1 rel -> T vs2 t2 rel -> T vs3 t3 rel -> T vs4 t4 rel -> T vs5 t5 rel
            -> AppliedM rel name modes '[vs1, vs2, vs3, vs4, vs5] '[t1, t2, t3, t4, t5])
mjudge5 modes format rules t1@(T _ _) t2@(T _ _) t3@(T _ _) t4@(T _ _) t5@(T _ _) =
  let args = t1 :! t2 :! t3 :! t4 :! t5 :! ANil
  in mjudge modes format rules args

mjudge6 :: forall name modes rel t1 t2 t3 t4 t5 t6.
           (Redex rel, KnownSymbol name, LogicType t1, LogicType t2, LogicType t3, LogicType t4, LogicType t5, LogicType t6)
        => ModeList modes
        -> ([String] -> String)
        -> [ModedRule rel '[t1, t2, t3, t4, t5, t6]]
        -> (forall vs1 vs2 vs3 vs4 vs5 vs6. (InputVars modes '[vs1, vs2, vs3, vs4, vs5, vs6] '[t1, t2, t3, t4, t5, t6], OutputVars modes '[vs1, vs2, vs3, vs4, vs5, vs6] '[t1, t2, t3, t4, t5, t6])
            => T vs1 t1 rel -> T vs2 t2 rel -> T vs3 t3 rel -> T vs4 t4 rel -> T vs5 t5 rel -> T vs6 t6 rel
            -> AppliedM rel name modes '[vs1, vs2, vs3, vs4, vs5, vs6] '[t1, t2, t3, t4, t5, t6])
mjudge6 modes format rules t1@(T _ _) t2@(T _ _) t3@(T _ _) t4@(T _ _) t5@(T _ _) t6@(T _ _) =
  let args = t1 :! t2 :! t3 :! t4 :! t5 :! t6 :! ANil
  in mjudge modes format rules args

-- | Define a unary moded judgment with scoped rule builder.
defJudge1 :: forall name modes rel t1.
             (RedexNeg rel, KnownSymbol name, LogicType t1, UnifyLList rel '[t1], SingModeList modes)
          => ([String] -> String)  -- ^ Format function
          -> ((forall n steps. CheckSchedule name steps
               => String -> RuleM rel '[t1] ('St 0 '[] 'False) ('St n steps 'True) ()
               -> ModedRule rel '[t1])
              -> [ModedRule rel '[t1]])
          -> (forall vs1. (InputVars modes '[vs1] '[t1], OutputVars modes '[vs1] '[t1])
              => T vs1 t1 rel -> AppliedM rel name modes '[vs1] '[t1])
defJudge1 format mkRules = mjudge1 singModeList format (mkRules rule)
  where
    rule :: forall n steps. CheckSchedule name steps
         => String -> RuleM rel '[t1] ('St 0 '[] 'False) ('St n steps 'True) ()
         -> ModedRule rel '[t1]
    rule = ruleM @name

defJudge2 :: forall name modes rel t1 t2.
             (RedexNeg rel, KnownSymbol name, LogicType t1, LogicType t2, UnifyLList rel '[t1, t2], SingModeList modes)
          => ([String] -> String)
          -> ((forall n steps. CheckSchedule name steps
               => String -> RuleM rel '[t1, t2] ('St 0 '[] 'False) ('St n steps 'True) ()
               -> ModedRule rel '[t1, t2])
              -> [ModedRule rel '[t1, t2]])
          -> (forall vs1 vs2. (InputVars modes '[vs1, vs2] '[t1, t2], OutputVars modes '[vs1, vs2] '[t1, t2])
              => T vs1 t1 rel -> T vs2 t2 rel
              -> AppliedM rel name modes '[vs1, vs2] '[t1, t2])
defJudge2 format mkRules = mjudge2 singModeList format (mkRules rule)
  where
    rule :: forall n steps. CheckSchedule name steps
         => String -> RuleM rel '[t1, t2] ('St 0 '[] 'False) ('St n steps 'True) ()
         -> ModedRule rel '[t1, t2]
    rule = ruleM @name

defJudge3 :: forall name modes rel t1 t2 t3.
             (RedexNeg rel, KnownSymbol name, LogicType t1, LogicType t2, LogicType t3, UnifyLList rel '[t1, t2, t3], SingModeList modes)
          => ([String] -> String)
          -> ((forall n steps. CheckSchedule name steps
               => String -> RuleM rel '[t1, t2, t3] ('St 0 '[] 'False) ('St n steps 'True) ()
               -> ModedRule rel '[t1, t2, t3])
              -> [ModedRule rel '[t1, t2, t3]])
          -> (forall vs1 vs2 vs3. (InputVars modes '[vs1, vs2, vs3] '[t1, t2, t3], OutputVars modes '[vs1, vs2, vs3] '[t1, t2, t3])
              => T vs1 t1 rel -> T vs2 t2 rel -> T vs3 t3 rel
              -> AppliedM rel name modes '[vs1, vs2, vs3] '[t1, t2, t3])
defJudge3 format mkRules = mjudge3 singModeList format (mkRules rule)
  where
    rule :: forall n steps. CheckSchedule name steps
         => String -> RuleM rel '[t1, t2, t3] ('St 0 '[] 'False) ('St n steps 'True) ()
         -> ModedRule rel '[t1, t2, t3]
    rule = ruleM @name

defJudge4 :: forall name modes rel t1 t2 t3 t4.
             (RedexNeg rel, KnownSymbol name, LogicType t1, LogicType t2, LogicType t3, LogicType t4, UnifyLList rel '[t1, t2, t3, t4], SingModeList modes)
          => ([String] -> String)
          -> ((forall n steps. CheckSchedule name steps
               => String -> RuleM rel '[t1, t2, t3, t4] ('St 0 '[] 'False) ('St n steps 'True) ()
               -> ModedRule rel '[t1, t2, t3, t4])
              -> [ModedRule rel '[t1, t2, t3, t4]])
          -> (forall vs1 vs2 vs3 vs4. (InputVars modes '[vs1, vs2, vs3, vs4] '[t1, t2, t3, t4], OutputVars modes '[vs1, vs2, vs3, vs4] '[t1, t2, t3, t4])
              => T vs1 t1 rel -> T vs2 t2 rel -> T vs3 t3 rel -> T vs4 t4 rel
              -> AppliedM rel name modes '[vs1, vs2, vs3, vs4] '[t1, t2, t3, t4])
defJudge4 format mkRules = mjudge4 singModeList format (mkRules rule)
  where
    rule :: forall n steps. CheckSchedule name steps
         => String -> RuleM rel '[t1, t2, t3, t4] ('St 0 '[] 'False) ('St n steps 'True) ()
         -> ModedRule rel '[t1, t2, t3, t4]
    rule = ruleM @name

defJudge5 :: forall name modes rel t1 t2 t3 t4 t5.
             (RedexNeg rel, KnownSymbol name, LogicType t1, LogicType t2, LogicType t3, LogicType t4, LogicType t5, UnifyLList rel '[t1, t2, t3, t4, t5], SingModeList modes)
          => ([String] -> String)
          -> ((forall n steps. CheckSchedule name steps
               => String -> RuleM rel '[t1, t2, t3, t4, t5] ('St 0 '[] 'False) ('St n steps 'True) ()
               -> ModedRule rel '[t1, t2, t3, t4, t5])
              -> [ModedRule rel '[t1, t2, t3, t4, t5]])
          -> (forall vs1 vs2 vs3 vs4 vs5. (InputVars modes '[vs1, vs2, vs3, vs4, vs5] '[t1, t2, t3, t4, t5], OutputVars modes '[vs1, vs2, vs3, vs4, vs5] '[t1, t2, t3, t4, t5])
              => T vs1 t1 rel -> T vs2 t2 rel -> T vs3 t3 rel -> T vs4 t4 rel -> T vs5 t5 rel
              -> AppliedM rel name modes '[vs1, vs2, vs3, vs4, vs5] '[t1, t2, t3, t4, t5])
defJudge5 format mkRules = mjudge5 singModeList format (mkRules rule)
  where
    rule :: forall n steps. CheckSchedule name steps
         => String -> RuleM rel '[t1, t2, t3, t4, t5] ('St 0 '[] 'False) ('St n steps 'True) ()
         -> ModedRule rel '[t1, t2, t3, t4, t5]
    rule = ruleM @name

defJudge6 :: forall name modes rel t1 t2 t3 t4 t5 t6.
             (RedexNeg rel, KnownSymbol name, LogicType t1, LogicType t2, LogicType t3, LogicType t4, LogicType t5, LogicType t6, UnifyLList rel '[t1, t2, t3, t4, t5, t6], SingModeList modes)
          => ([String] -> String)
          -> ((forall n steps. CheckSchedule name steps
               => String -> RuleM rel '[t1, t2, t3, t4, t5, t6] ('St 0 '[] 'False) ('St n steps 'True) ()
               -> ModedRule rel '[t1, t2, t3, t4, t5, t6])
              -> [ModedRule rel '[t1, t2, t3, t4, t5, t6]])
          -> (forall vs1 vs2 vs3 vs4 vs5 vs6. (InputVars modes '[vs1, vs2, vs3, vs4, vs5, vs6] '[t1, t2, t3, t4, t5, t6], OutputVars modes '[vs1, vs2, vs3, vs4, vs5, vs6] '[t1, t2, t3, t4, t5, t6])
              => T vs1 t1 rel -> T vs2 t2 rel -> T vs3 t3 rel -> T vs4 t4 rel -> T vs5 t5 rel -> T vs6 t6 rel
              -> AppliedM rel name modes '[vs1, vs2, vs3, vs4, vs5, vs6] '[t1, t2, t3, t4, t5, t6])
defJudge6 format mkRules = mjudge6 singModeList format (mkRules rule)
  where
    rule :: forall n steps. CheckSchedule name steps
         => String -> RuleM rel '[t1, t2, t3, t4, t5, t6] ('St 0 '[] 'False) ('St n steps 'True) ()
         -> ModedRule rel '[t1, t2, t3, t4, t5, t6]
    rule = ruleM @name

-- | Convert AppliedM to Applied for running queries.
toApplied :: AppliedM rel name modes vss ts -> Applied rel ts
toApplied (AppliedM goal name args _ _ _) = Applied args goal name

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
concl :: forall name modes rel vss ts n steps.
         (Redex rel, UnifyLList rel ts)
      => AppliedM rel name modes vss ts
      -> RuleM rel ts ('St n steps 'False)
                   ('St n (Snoc steps ('ConcStep name (ReqVars modes vss) (ProdVars modes vss))) 'True) ()
concl applied = RuleM $ \env -> do
  markConclusion
  unifyLList (amArgs applied) (reArgs env)
  pure ((), env { reAvailVars = amReqVars applied })

captureArgs :: LTermList rel ts -> [CapturedTerm rel]
captureArgs TNil = []
captureArgs (x :> xs) = CapturedTerm x : captureArgs xs

-- | Declare premise. Collects for later execution.
prem :: forall name modes rel vss ts ts' n steps c.
        Redex rel
     => AppliedM rel name modes vss ts'
     -> RuleM rel ts ('St n steps c)
                  ('St n (Snoc steps ('PremStep ('Goal name (ReqVars modes vss) (ProdVars modes vss)))) c) ()
prem applied = RuleM $ \env -> do
  markPremise (amName applied) (captureArgs (amArgs applied)) (amFormat applied)
  -- Wrap the premise goal in a synthetic "__goal__" relation call.
  --
  -- This is a no-op for normal execution (it just calls the underlying goal),
  -- but it gives tracing interpreters a stable call boundary for producing
  -- premise-level diagnostics when the goal has no solutions.
  --
  -- The tracing pretty-printer treats rule name "__goal__" as transparent, so this
  -- wrapper does not clutter successful derivations.
  let wrappedGoal =
        call $ Relation (amName applied) "__goal__" (captureArgs (amArgs applied)) (amGoal applied) (amFormat applied)
  pure
    ( ()
    , env { reDeferred = PremA (PremAction (amReqVars applied) (amProdVars applied) wrappedGoal) : reDeferred env }
    )

-- | Declare negation-as-failure. The goal must fail for the rule to succeed.
neg :: forall name modes rel vss ts ts' n steps c.
       Redex rel
    => AppliedM rel name modes vss ts'
    -> RuleM rel ts ('St n steps c)
                 ('St n (Snoc steps ('NegStep (AllVars modes vss))) c) ()
neg applied = RuleM $ \env -> pure
  ( ()
  , env { reDeferred = NegA (NegAction (S.union (amReqVars applied) (amProdVars applied)) (amGoal applied)) : reDeferred env }
  )

-- | Equality constraint: both arguments must be ground.
infix 4 ===
(===) :: forall a rel ts vs1 vs2 n steps c.
         (Redex rel, LogicType a, Typeable a)
      => T vs1 a rel -> T vs2 a rel
      -> RuleM rel ts ('St n steps c)
                   ('St n (Snoc steps ('PremStep ('Goal "==" (Union vs1 vs2) '[]))) c) ()
(===) (T vars1 t1) (T vars2 t2) = RuleM $ \env -> do
  markPremise "==" [CapturedTerm t1, CapturedTerm t2] eqFmt
  pure ( ()
       , env { reDeferred = PremA (PremAction (S.union vars1 vars2) S.empty (t1 <=> t2))
             : reDeferred env }
       )
  where eqFmt [a, b] = a ++ " = " ++ b
        eqFmt args = "==(" ++ intercalate ", " args ++ ")"
        intercalate _ [] = ""
        intercalate _ [x] = x
        intercalate sep (x:xs) = x ++ sep ++ intercalate sep xs

-- | Inequality constraint: both arguments must be ground.
infix 4 =/=
(=/=) :: forall a rel ts vs1 vs2 n steps c.
         (RedexNeg rel, LogicType a, Typeable a)
      => T vs1 a rel -> T vs2 a rel
      -> RuleM rel ts ('St n steps c)
                   ('St n (Snoc steps ('PremStep ('Goal "=/=" (Union vs1 vs2) '[]))) c) ()
(=/=) (T vars1 t1) (T vars2 t2) = RuleM $ \env -> do
  markPremise "=/=" [CapturedTerm t1, CapturedTerm t2] neqFmt
  pure ( ()
       , env { reDeferred = PremA (PremAction (S.union vars1 vars2) S.empty (R.neg (t1 <=> t2)))
             : reDeferred env }
       )
  where neqFmt [a, b] = a ++ " ≠ " ++ b
        neqFmt args = "=/=(" ++ intercalate ", " args ++ ")"
        intercalate _ [] = ""
        intercalate _ [x] = x
        intercalate sep (x:xs) = x ++ sep ++ intercalate sep xs

--------------------------------------------------------------------------------
-- Schedule Checking (Batch Algorithm)
--
-- Uses O(k · p · n) algorithm where k = number of dependency stages
-- Instead of selecting one goal at a time, partitions all goals into
-- (ready, notReady) and processes all ready goals in a single step.
--------------------------------------------------------------------------------

type family ConclVars (steps :: [Step]) :: [Nat] where
  ConclVars ('ConcStep _ ins _ ': _) = ins
  ConclVars (_ ': rest) = ConclVars rest
  ConclVars '[] = TypeError ('Text "Rule is missing a conclusion (concl)")

type family ConclOutVars (steps :: [Step]) :: [Nat] where
  ConclOutVars ('ConcStep _ _ outs ': _) = outs
  ConclOutVars (_ ': rest) = ConclOutVars rest
  ConclOutVars '[] = TypeError ('Text "Rule is missing a conclusion (concl)")

type family PremGoals (steps :: [Step]) :: [Goal] where
  PremGoals '[] = '[]
  PremGoals ('PremStep g ': rest) = g ': PremGoals rest
  PremGoals ('ConcStep _ _ _ ': rest) = PremGoals rest
  PremGoals ('NegStep _ ': rest) = PremGoals rest

type family NegReqs (steps :: [Step]) :: [[Nat]] where
  NegReqs '[] = '[]
  NegReqs ('NegStep req ': rest) = req ': NegReqs rest
  NegReqs ('PremStep _ ': rest) = NegReqs rest
  NegReqs ('ConcStep _ _ _ ': rest) = NegReqs rest

-- | Collect all output variables from a list of goals
type family CollectOutputs (gs :: [Goal]) :: [Nat] where
  CollectOutputs '[] = '[]
  CollectOutputs ('Goal _ _ prod ': rest) = Union prod (CollectOutputs rest)

type family FinalAvail (steps :: [Step]) :: [Nat] where
  FinalAvail steps = Union (ConclVars steps) (CollectOutputs (PremGoals steps))

-- | Check if a goal is ready (inputs ⊆ available)
type family IsReady (avail :: [Nat]) (g :: Goal) :: Bool where
  IsReady avail ('Goal _ req _) = Subset req avail

-- | Partition goals into (ready, notReady) in a single pass. O(p · n)
type family Partition (avail :: [Nat]) (gs :: [Goal]) :: ([Goal], [Goal]) where
  Partition _ '[] = '( '[], '[] )
  Partition avail (g ': gs) = PartitionStep (IsReady avail g) g (Partition avail gs)

type family PartitionStep (ready :: Bool) (g :: Goal) (rest :: ([Goal], [Goal])) :: ([Goal], [Goal]) where
  PartitionStep 'True  g '( ready, notReady ) = '( g ': ready, notReady )
  PartitionStep 'False g '( ready, notReady ) = '( ready, g ': notReady )

-- | Batch scheduling result
data SolveResult = Solved | Stuck [Nat] [Goal]

-- | Batch solve: process all ready goals at once, then recurse
type family Solve (avail :: [Nat]) (pending :: [Goal]) :: SolveResult where
  Solve _ '[] = 'Solved
  Solve avail pending = SolveStep (Partition avail pending) avail

type family SolveStep (partition :: ([Goal], [Goal])) (avail :: [Nat]) :: SolveResult where
  SolveStep '( '[], notReady ) avail = 'Stuck avail notReady  -- No progress, stuck!
  SolveStep '( ready, notReady ) avail = Solve (Union avail (CollectOutputs ready)) notReady

-- | Main schedule checking constraint
type family CheckSchedule (name :: Symbol) (steps :: [Step]) :: Constraint where
  CheckSchedule name steps =
    ( CheckPremises name steps (Solve (ConclVars steps) (PremGoals steps))
    , CheckNegations name steps (FinalAvail steps) (NegReqs steps)
    , CheckOutputsCovered name (ConclOutVars steps) (FinalAvail steps)
    )

type family CheckPremises (name :: Symbol) (steps :: [Step]) (r :: SolveResult) :: Constraint where
  CheckPremises _ _ 'Solved = ()
  CheckPremises name _ ('Stuck avail gs) = TypeError
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

type family CheckOutputsCovered (name :: Symbol) (outs :: [Nat]) (avail :: [Nat]) :: Constraint where
  CheckOutputsCovered name outs avail =
    If (Subset outs avail)
       (() :: Constraint)
       (TypeError
         ( 'Text "In rule \"" ':<>: 'Text name ':<>: 'Text "\": conclusion outputs not grounded"
             ':$$: 'Text ""
             ':$$: 'Text "  Conclusion output variables: " ':<>: 'ShowType outs
             ':$$: 'Text "  Grounded after premises:     " ':<>: 'ShowType avail
             ':$$: 'Text "  Ungrounded (ghost vars):     " ':<>: 'ShowType (Diff outs avail)
             ':$$: 'Text ""
             ':$$: 'Text "  (Variable indices are assigned by fresh in declaration order: 0, 1, 2, ...)"
             ':$$: 'Text ""
             ':$$: 'Text "  To fix: ensure output variables appear in a premise's output position,"
             ':$$: 'Text "          or reuse a variable from the conclusion's input positions."
         ))

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
  if skipLiftedActions (Proxy :: Proxy rel) then pure () else executeLifted lifted

-- | Partition deferred actions into premises, negations, and lifted actions.
partitionDeferred :: [DeferredAction rel] -> ([PremAction rel], [NegAction rel], [rel ()])
partitionDeferred = foldr go ([], [], [])
  where
    go (PremA p)   (ps, ns, ls) = (p:ps, ns, ls)
    go (NegA n)    (ps, ns, ls) = (ps, n:ns, ls)
    go (LiftedA l) (ps, ns, ls) = (ps, ns, l:ls)

-- | Execute negations in source order.
executeNegations :: RedexNeg rel => [NegAction rel] -> rel ()
executeNegations [] = pure ()
executeNegations (n:ns) = R.neg (naGoal n) Prelude.>> executeNegations ns

-- | Execute lifted actions in order.
executeLifted :: Redex rel => [rel ()] -> rel ()
executeLifted [] = pure ()
executeLifted (a:as) = a Prelude.>> executeLifted as
