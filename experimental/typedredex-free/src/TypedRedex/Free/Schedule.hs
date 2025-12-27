{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}

-- | Type-Level Schedule Checking for Mode-Guided Execution
--
-- This module provides compile-time verification that all rules have
-- valid execution schedules. It checks:
--
-- 1. All premises can be scheduled (inputs are grounded)
-- 2. All negations have grounded inputs
-- 3. All conclusion outputs are produced
--
-- = Type-Level Representations
--
-- @
-- data St = St Nat [Step] Bool
--   Nat   : next fresh variable ID
--   [Step]: accumulated operations
--   Bool  : has conclusion been declared?
--
-- data Step
--   = ConcStep Symbol [Nat] [Nat]   -- name, inputs, outputs
--   | PremStep Goal
--   | NegStep [Nat]
--
-- data Goal = Goal Symbol [Nat] [Nat]  -- name, required, produced
-- @
module TypedRedex.Free.Schedule
  ( -- * State Kinds
    St(..)
  , Step(..)
  , Goal(..)
    -- * Mode Types
  , Mode(..)
  , ModeList(..)
  , SingModeList(..)
    -- * Type Families for Mode Analysis
  , ReqVars
  , ProdVars
  , AllVars
    -- * Type-Level Set Operations
  , Union
  , Diff
  , Subset
  , Elem
  , Snoc
    -- * Schedule Checking
  , CheckSchedule
  , SolveResult(..)
  ) where

import GHC.TypeLits (TypeError, ErrorMessage(..), Symbol, Nat, type (+))
import Data.Kind (Constraint)

--------------------------------------------------------------------------------
-- Mode Types
--------------------------------------------------------------------------------

-- | Mode annotation: Input or Output
data Mode = I | O
  deriving (Eq, Show)

-- | Type-level list of modes
data ModeList (ms :: [Mode]) where
  MNil  :: ModeList '[]
  (:*)  :: Mode -> ModeList ms -> ModeList (m ': ms)

infixr 5 :*

-- | Singleton for deriving term-level ModeList from type-level
class SingModeList (ms :: [Mode]) where
  singModeList :: ModeList ms

instance SingModeList '[] where
  singModeList = MNil

instance SingModeList ms => SingModeList ('I ': ms) where
  singModeList = I :* singModeList

instance SingModeList ms => SingModeList ('O ': ms) where
  singModeList = O :* singModeList

--------------------------------------------------------------------------------
-- State Machine Types
--------------------------------------------------------------------------------

-- | Rule state: (nextVar, steps, hasConclusion)
data St = St Nat [Step] Bool

-- | A step in rule construction
data Step
  = ConcStep Symbol [Nat] [Nat]   -- ^ Conclusion: name, input vars, output vars
  | PremStep Goal                 -- ^ Premise
  | NegStep [Nat]                 -- ^ Negation: required vars

-- | A premise goal
data Goal = Goal Symbol [Nat] [Nat]  -- ^ name, required vars, produced vars

--------------------------------------------------------------------------------
-- Type-Level Set Operations
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
-- Mode Analysis
--------------------------------------------------------------------------------

-- | Extract input variables (mode I positions)
type family ReqVars (modes :: [Mode]) (vss :: [[Nat]]) :: [Nat] where
  ReqVars '[] '[] = '[]
  ReqVars ('I ': ms) (vs ': vss) = Union vs (ReqVars ms vss)
  ReqVars ('O ': ms) (_ ': vss) = ReqVars ms vss
  ReqVars _ _ = TypeError ('Text "Mode list length mismatch")

-- | Extract output variables (mode O positions)
type family ProdVars (modes :: [Mode]) (vss :: [[Nat]]) :: [Nat] where
  ProdVars '[] '[] = '[]
  ProdVars ('I ': ms) (_ ': vss) = ProdVars ms vss
  ProdVars ('O ': ms) (vs ': vss) = Union vs (ProdVars ms vss)
  ProdVars _ _ = TypeError ('Text "Mode list length mismatch")

-- | All variables in all positions
type family AllVars (modes :: [Mode]) (vss :: [[Nat]]) :: [Nat] where
  AllVars modes vss = Union (ReqVars modes vss) (ProdVars modes vss)

--------------------------------------------------------------------------------
-- Schedule Analysis
--------------------------------------------------------------------------------

-- | Extract conclusion input variables
type family ConclVars (steps :: [Step]) :: [Nat] where
  ConclVars ('ConcStep _ ins _ ': _) = ins
  ConclVars (_ ': rest) = ConclVars rest
  ConclVars '[] = TypeError ('Text "Rule is missing a conclusion (concl)")

-- | Extract conclusion output variables
type family ConclOutVars (steps :: [Step]) :: [Nat] where
  ConclOutVars ('ConcStep _ _ outs ': _) = outs
  ConclOutVars (_ ': rest) = ConclOutVars rest
  ConclOutVars '[] = TypeError ('Text "Rule is missing a conclusion")

-- | Extract all premise goals
type family PremGoals (steps :: [Step]) :: [Goal] where
  PremGoals '[] = '[]
  PremGoals ('PremStep g ': rest) = g ': PremGoals rest
  PremGoals ('ConcStep _ _ _ ': rest) = PremGoals rest
  PremGoals ('NegStep _ ': rest) = PremGoals rest

-- | Extract negation requirements
type family NegReqs (steps :: [Step]) :: [[Nat]] where
  NegReqs '[] = '[]
  NegReqs ('NegStep req ': rest) = req ': NegReqs rest
  NegReqs ('PremStep _ ': rest) = NegReqs rest
  NegReqs ('ConcStep _ _ _ ': rest) = NegReqs rest

-- | Collect all variables produced by premises
type family AllPremProds (gs :: [Goal]) :: [Nat] where
  AllPremProds '[] = '[]
  AllPremProds ('Goal _ _ prod ': rest) = Union prod (AllPremProds rest)

-- | Variables available after all premises
type family FinalAvail (steps :: [Step]) :: [Nat] where
  FinalAvail steps = Union (ConclVars steps) (AllPremProds (PremGoals steps))

--------------------------------------------------------------------------------
-- Solving (Topological Sort)
--------------------------------------------------------------------------------

-- | Result of solving premises
data SolveResult = Solved | Stuck [Nat] [Goal]

-- | Check if a goal is ready (all inputs available)
type family Ready (avail :: [Nat]) (g :: Goal) :: Bool where
  Ready avail ('Goal _ req _) = Subset req avail

-- | Select a ready goal from the list
type family SelectReady (avail :: [Nat]) (gs :: [Goal]) :: Maybe (Goal, [Goal]) where
  SelectReady _ '[] = 'Nothing
  SelectReady avail (g ': gs) =
    If (Ready avail g)
       ('Just '(g, gs))
       (PrependMaybe g (SelectReady avail gs))

type family PrependMaybe (g :: Goal) (m :: Maybe (Goal, [Goal])) :: Maybe (Goal, [Goal]) where
  PrependMaybe _ 'Nothing = 'Nothing
  PrependMaybe g ('Just '(g1, rest)) = 'Just '(g1, g ': rest)

-- | Solve: try to schedule all premises
type family Solve (avail :: [Nat]) (gs :: [Goal]) :: SolveResult where
  Solve _ '[] = 'Solved
  Solve avail gs = SolveStep (SelectReady avail gs) avail gs

type family SolveStep (m :: Maybe (Goal, [Goal])) (avail :: [Nat]) (gs :: [Goal]) :: SolveResult where
  SolveStep 'Nothing avail gs = 'Stuck avail gs
  SolveStep ('Just '( 'Goal _ _ prod, rest)) avail _ = Solve (Union avail prod) rest

--------------------------------------------------------------------------------
-- Main Check
--------------------------------------------------------------------------------

-- | Main schedule checking constraint
--
-- Checks:
-- 1. All premises can be scheduled
-- 2. All negations have grounded inputs
-- 3. All conclusion outputs are produced
type family CheckSchedule (name :: Symbol) (steps :: [Step]) :: Constraint where
  CheckSchedule name steps =
    ( CheckPremises name steps (Solve (ConclVars steps) (PremGoals steps))
    , CheckNegations name steps (FinalAvail steps) (NegReqs steps)
    , CheckOutputsCovered name (ConclOutVars steps) (FinalAvail steps)
    )

-- | Check that premises can be scheduled
type family CheckPremises (name :: Symbol) (steps :: [Step]) (r :: SolveResult) :: Constraint where
  CheckPremises _ _ 'Solved = ()
  CheckPremises name steps ('Stuck avail gs) = TypeError
    ( 'Text "In rule \"" ':<>: 'Text name ':<>: 'Text "\": cannot schedule premises"
        ':$$: 'Text ""
        ':$$: 'Text "  Grounded variables: " ':<>: 'ShowType avail
        ':$$: 'Text "  Blocked premises:"
        ':$$: ShowBlocked avail gs
        ':$$: 'Text ""
        ':$$: 'Text "  (Variable indices assigned by fresh: 0, 1, 2, ...)"
        ':$$: 'Text ""
        ':$$: 'Text "  Fix: ensure each premise's inputs are grounded by"
        ':$$: 'Text "       the conclusion or prior premise outputs."
    )

-- | Check that conclusion outputs are covered
type family CheckOutputsCovered (name :: Symbol) (outs :: [Nat]) (avail :: [Nat]) :: Constraint where
  CheckOutputsCovered name outs avail =
    If (Subset outs avail)
       (() :: Constraint)
       (TypeError
         ( 'Text "In rule \"" ':<>: 'Text name ':<>: 'Text "\": outputs not grounded"
             ':$$: 'Text ""
             ':$$: 'Text "  Conclusion outputs: " ':<>: 'ShowType outs
             ':$$: 'Text "  Available:          " ':<>: 'ShowType avail
             ':$$: 'Text "  Ungrounded:         " ':<>: 'ShowType (Diff outs avail)
         ))

-- | Check that negations have grounded inputs
type family CheckNegations (name :: Symbol) (steps :: [Step]) (avail :: [Nat]) (negs :: [[Nat]]) :: Constraint where
  CheckNegations _ _ _ '[] = ()
  CheckNegations name steps avail (req ': rest) =
    If (Subset req avail)
       (CheckNegations name steps avail rest)
       (TypeError
         ( 'Text "In rule \"" ':<>: 'Text name ':<>: 'Text "\": negation ungrounded"
             ':$$: 'Text ""
             ':$$: 'Text "  Available: " ':<>: 'ShowType avail
             ':$$: 'Text "  Required:  " ':<>: 'ShowType req
             ':$$: 'Text "  Missing:   " ':<>: 'ShowType (Diff req avail)
         ))

-- | Show blocked premises for error message
type family ShowBlocked (avail :: [Nat]) (gs :: [Goal]) :: ErrorMessage where
  ShowBlocked _ '[] = 'Text ""
  ShowBlocked avail ('Goal name req _ ': rest) =
    ('Text "    - " ':<>: 'Text name ':<>: 'Text ": needs " ':<>: 'ShowType (Diff req avail))
      ':$$: ShowBlocked avail rest
