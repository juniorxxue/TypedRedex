-- | Compile-time schedule checking for mode-guided execution
--
-- Verifies at compile time:
--   1. All premises can be scheduled (inputs grounded)
--   2. All negations have grounded inputs
--   3. All conclusion outputs are produced
module TypedRedex.Core.Schedule
  ( -- * State kinds
    St(..), Step(..), Goal(..)
  -- * Mode types
  , Mode(..), ModeList(..), SingModeList(..)
  -- * Type families
  , ReqVars, ProdVars, AllVars
  , Union, Snoc
  -- * Schedule checking
  , CheckSchedule
  ) where

import GHC.TypeLits (TypeError, ErrorMessage(..), Symbol, Nat)
import Data.Kind (Constraint)

--------------------------------------------------------------------------------
-- Mode types
--------------------------------------------------------------------------------

data Mode = I | O deriving (Eq, Show)

data ModeList (ms :: [Mode]) where
  MNil :: ModeList '[]
  (:*) :: Mode -> ModeList ms -> ModeList (m ': ms)
infixr 5 :*

class SingModeList (ms :: [Mode]) where
  singModeList :: ModeList ms

instance SingModeList '[] where singModeList = MNil
instance SingModeList ms => SingModeList ('I ': ms) where singModeList = I :* singModeList
instance SingModeList ms => SingModeList ('O ': ms) where singModeList = O :* singModeList

--------------------------------------------------------------------------------
-- State machine types
--------------------------------------------------------------------------------

-- | Rule state: (nextVar, steps, hasConclusion)
data St = St Nat [Step] Bool

data Step
  = ConcStep Symbol [Nat] [Nat]  -- ^ name, inputs, outputs
  | PremStep Goal                 -- ^ premise
  | NegStep [Nat]                 -- ^ negation: required vars

data Goal = Goal Symbol [Nat] [Nat]  -- ^ name, required, produced

--------------------------------------------------------------------------------
-- Set operations
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
-- Mode analysis
--------------------------------------------------------------------------------

type family ReqVars (modes :: [Mode]) (vss :: [[Nat]]) :: [Nat] where
  ReqVars '[] '[] = '[]
  ReqVars ('I ': ms) (vs ': vss) = Union vs (ReqVars ms vss)
  ReqVars ('O ': ms) (_ ': vss) = ReqVars ms vss

type family ProdVars (modes :: [Mode]) (vss :: [[Nat]]) :: [Nat] where
  ProdVars '[] '[] = '[]
  ProdVars ('I ': ms) (_ ': vss) = ProdVars ms vss
  ProdVars ('O ': ms) (vs ': vss) = Union vs (ProdVars ms vss)

type family AllVars (modes :: [Mode]) (vss :: [[Nat]]) :: [Nat] where
  AllVars modes vss = Union (ReqVars modes vss) (ProdVars modes vss)

--------------------------------------------------------------------------------
-- Schedule analysis
--------------------------------------------------------------------------------

type family ConclVars (steps :: [Step]) :: [Nat] where
  ConclVars ('ConcStep _ ins _ ': _) = ins
  ConclVars (_ ': rest) = ConclVars rest
  ConclVars '[] = TypeError ('Text "Rule missing conclusion")

type family ConclOutVars (steps :: [Step]) :: [Nat] where
  ConclOutVars ('ConcStep _ _ outs ': _) = outs
  ConclOutVars (_ ': rest) = ConclOutVars rest
  ConclOutVars '[] = '[]

type family PremGoals (steps :: [Step]) :: [Goal] where
  PremGoals '[] = '[]
  PremGoals ('PremStep g ': rest) = g ': PremGoals rest
  PremGoals (_ ': rest) = PremGoals rest

type family NegReqs (steps :: [Step]) :: [[Nat]] where
  NegReqs '[] = '[]
  NegReqs ('NegStep req ': rest) = req ': NegReqs rest
  NegReqs (_ ': rest) = NegReqs rest

type family AllPremProds (gs :: [Goal]) :: [Nat] where
  AllPremProds '[] = '[]
  AllPremProds ('Goal _ _ prod ': rest) = Union prod (AllPremProds rest)

type family FinalAvail (steps :: [Step]) :: [Nat] where
  FinalAvail steps = Union (ConclVars steps) (AllPremProds (PremGoals steps))

--------------------------------------------------------------------------------
-- Solving (topological sort)
--------------------------------------------------------------------------------

data SolveResult = Solved | Stuck [Nat] [Goal]

type family Ready (avail :: [Nat]) (g :: Goal) :: Bool where
  Ready avail ('Goal _ req _) = Subset req avail

type family SelectReady (avail :: [Nat]) (gs :: [Goal]) :: Maybe (Goal, [Goal]) where
  SelectReady _ '[] = 'Nothing
  SelectReady avail (g ': gs) =
    If (Ready avail g)
       ('Just '(g, gs))
       (PrependMaybe g (SelectReady avail gs))

type family PrependMaybe (g :: Goal) (m :: Maybe (Goal, [Goal])) :: Maybe (Goal, [Goal]) where
  PrependMaybe _ 'Nothing = 'Nothing
  PrependMaybe g ('Just '(h, rest)) = 'Just '(h, g ': rest)

type family Solve (avail :: [Nat]) (gs :: [Goal]) :: SolveResult where
  Solve _ '[] = 'Solved
  Solve avail gs = SolveStep (SelectReady avail gs) avail gs

type family SolveStep (m :: Maybe (Goal, [Goal])) (avail :: [Nat]) (gs :: [Goal]) :: SolveResult where
  SolveStep 'Nothing avail gs = 'Stuck avail gs
  SolveStep ('Just '( 'Goal _ _ prod, rest)) avail _ = Solve (Union avail prod) rest

--------------------------------------------------------------------------------
-- Main constraint
--------------------------------------------------------------------------------

type family CheckSchedule (name :: Symbol) (steps :: [Step]) :: Constraint where
  CheckSchedule name steps =
    ( CheckPremises name (Solve (ConclVars steps) (PremGoals steps))
    , CheckNegations name (FinalAvail steps) (NegReqs steps)
    , CheckOutputs name (ConclOutVars steps) (FinalAvail steps)
    )

type family CheckPremises (name :: Symbol) (r :: SolveResult) :: Constraint where
  CheckPremises _ 'Solved = ()
  CheckPremises name ('Stuck avail gs) = TypeError
    ( 'Text "Rule \"" ':<>: 'Text name ':<>: 'Text "\": cannot schedule premises"
        ':$$: 'Text "  Available: " ':<>: 'ShowType avail
        ':$$: 'Text "  Blocked: " ':<>: 'ShowType gs
    )

type family CheckOutputs (name :: Symbol) (outs :: [Nat]) (avail :: [Nat]) :: Constraint where
  CheckOutputs name outs avail =
    If (Subset outs avail) (() :: Constraint)
       (TypeError ('Text "Rule \"" ':<>: 'Text name ':<>: 'Text "\": outputs ungrounded: " ':<>: 'ShowType (Diff outs avail)))

type family CheckNegations (name :: Symbol) (avail :: [Nat]) (negs :: [[Nat]]) :: Constraint where
  CheckNegations _ _ '[] = ()
  CheckNegations name avail (req ': rest) =
    If (Subset req avail)
       (CheckNegations name avail rest)
       (TypeError ('Text "Rule \"" ':<>: 'Text name ':<>: 'Text "\": negation needs: " ':<>: 'ShowType (Diff req avail)))
