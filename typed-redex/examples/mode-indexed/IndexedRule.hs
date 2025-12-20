{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}

-- | Minimal demo: indexed-monad + QualifiedDo + mode checking.
--
-- This is intentionally *not* a solver. It only builds a typed rule body and
-- rejects ill-moded rules at compile time.
module IndexedRule
  ( -- * Modes
    Mode(..)
    -- * Terms
  , Term, unit, pair
    -- * Calls (predicates)
  , Call
  , h, q, p
    -- * Rule DSL
  , Rule, rule
  , RuleM
  , fresh, prem, concl
    -- * QualifiedDo operators
  , return, (>>=), (>>), fail
  ) where

import Prelude hiding ((>>=), (>>), return, fail)
import Data.Kind (Constraint, Type)
import GHC.TypeLits (TypeError, ErrorMessage(..), Symbol)
import GHC.TypeNats (Nat, type (+))

--------------------------------------------------------------------------------
-- Modes
--------------------------------------------------------------------------------

data Mode = I | O

--------------------------------------------------------------------------------
-- Terms (only carry the set of variables they mention, at the type level)
--------------------------------------------------------------------------------

-- | A variable token (singleton).
data V (n :: Nat) = V

-- | A term annotated with the type-level set of variables it mentions.
data Term (vs :: [Nat]) where
  TVar  :: V n -> Term '[n]
  TUnit :: Term '[]
  TPair :: Term as -> Term bs -> Term (Union as bs)

unit :: Term '[]
unit = TUnit

pair :: Term as -> Term bs -> Term (Union as bs)
pair = TPair

--------------------------------------------------------------------------------
-- Predicate calls
--------------------------------------------------------------------------------

data Pred (name :: Symbol) (modes :: [Mode]) where
  Pred :: Pred name modes

data Args (as :: [[Nat]]) where
  ANil :: Args '[]
  (:>) :: Term a -> Args as -> Args (a ': as)
infixr 5 :>

data Call (name :: Symbol) (modes :: [Mode]) (as :: [[Nat]]) where
  Call :: Pred name modes -> Args as -> Call name modes as

-- Example predicates:
--   h : I
--   q : I
--   p : I,O  (produces its second arg)
h :: Term a -> Call "h" '[I] '[a]
h a = Call Pred (a :> ANil)

q :: Term a -> Call "q" '[I] '[a]
q a = Call Pred (a :> ANil)

p :: Term a -> Term b -> Call "p" '[I, O] '[a, b]
p a b = Call Pred (a :> b :> ANil)

--------------------------------------------------------------------------------
-- Rule DSL as an indexed monad (Atkey-style)
--------------------------------------------------------------------------------

data Goal = Goal Symbol [Nat] [Nat]   -- predicate name, requires, produces
data Step = Concl Symbol [Nat] | Prem Goal

-- | Indexed state: next fresh var, collected steps, and whether concl was seen.
data St = St Nat [Step] Bool

newtype RuleM (s :: St) (t :: St) a = RuleM a

return :: a -> RuleM s s a
return = RuleM

(>>=) :: RuleM s t a -> (a -> RuleM t u b) -> RuleM s u b
RuleM a >>= f = case f a of
  RuleM b -> RuleM b

(>>) :: RuleM s t a -> RuleM t u b -> RuleM s u b
m >> k = m >>= \_ -> k

fail :: String -> RuleM s t a
fail msg = RuleM (error msg)

-- | Fresh variable (initially not ground).
fresh :: RuleM ('St n steps c) ('St (n + 1) steps c) (Term '[n])
fresh = RuleM (TVar V)

-- | Add a premise call (does not execute anything; records mode requirements).
prem
  :: Call name modes as
  -> RuleM
      ('St n steps c)
      ('St n (Snoc steps ('Prem ('Goal name (ReqVars modes as) (ProdVars modes as)))) c)
      ()
prem _ = RuleM ()

-- | Declare the conclusion/head pattern.
--   The head runs first and grounds variables appearing in input positions.
concl
  :: Call name modes as
  -> RuleM
      ('St n steps 'False)
      ('St n (Snoc steps ('Concl name (ReqVars modes as))) 'True)
      ()
concl _ = RuleM ()

data Rule (steps :: [Step]) where
  Rule :: Rule steps

-- | Close a rule: requires exactly one concl (tracked by the Bool index) and a
-- schedulable set of premises (mode-check).
rule
  :: CheckSchedule steps
  => RuleM ('St 0 '[] 'False) ('St n steps 'True) ()
  -> Rule steps
rule _ = Rule

--------------------------------------------------------------------------------
-- Type-level mode analysis
--------------------------------------------------------------------------------

type family If (b :: Bool) (t :: k) (f :: k) :: k where
  If 'True  t _ = t
  If 'False _ f = f

type family And (a :: Bool) (b :: Bool) :: Bool where
  And 'True  b = b
  And 'False _ = 'False

type family Elem (x :: Nat) (xs :: [Nat]) :: Bool where
  Elem _ '[]       = 'False
  Elem x (x ': xs) = 'True
  Elem x (_ ': xs) = Elem x xs

type family Insert (x :: Nat) (xs :: [Nat]) :: [Nat] where
  Insert x xs = If (Elem x xs) xs (x ': xs)

type family Union (xs :: [Nat]) (ys :: [Nat]) :: [Nat] where
  Union '[]       ys = ys
  Union (x ': xs) ys = Union xs (Insert x ys)

type family Subset (xs :: [Nat]) (ys :: [Nat]) :: Bool where
  Subset '[]       _  = 'True
  Subset (x ': xs) ys = And (Elem x ys) (Subset xs ys)

type family ReqVars (modes :: [Mode]) (as :: [[Nat]]) :: [Nat] where
  ReqVars '[]       '[]       = '[]
  ReqVars ('I ': ms) (a ': as) = Union a (ReqVars ms as)
  ReqVars ('O ': ms) (_ ': as) = ReqVars ms as
  ReqVars ms as =
    TypeError
      ( 'Text "ReqVars: mode/arg length mismatch."
          ':$$: 'Text "  modes: " ':<>: 'ShowType ms
          ':$$: 'Text "  args : " ':<>: 'ShowType as
      )

type family ProdVars (modes :: [Mode]) (as :: [[Nat]]) :: [Nat] where
  ProdVars '[]       '[]       = '[]
  ProdVars ('I ': ms) (_ ': as) = ProdVars ms as
  ProdVars ('O ': ms) (a ': as) = Union a (ProdVars ms as)
  ProdVars ms as =
    TypeError
      ( 'Text "ProdVars: mode/arg length mismatch."
          ':$$: 'Text "  modes: " ':<>: 'ShowType ms
          ':$$: 'Text "  args : " ':<>: 'ShowType as
      )

type family ConclVars (steps :: [Step]) :: [Nat] where
  ConclVars ('Concl _name vs ': _) = vs
  ConclVars (_ ': rest) = ConclVars rest
  ConclVars '[] = TypeError ('Text "Internal error: concl missing from steps")

type family ConclName (steps :: [Step]) :: Symbol where
  ConclName ('Concl name _vs ': _) = name
  ConclName (_ ': rest) = ConclName rest
  ConclName '[] = TypeError ('Text "Internal error: concl missing from steps")

type family PremGoals (steps :: [Step]) :: [Goal] where
  PremGoals '[] = '[]
  PremGoals ('Prem g ': rest) = g ': PremGoals rest
  PremGoals ('Concl _name _vs ': rest) = PremGoals rest

type family Ready (avail :: [Nat]) (g :: Goal) :: Bool where
  Ready avail ('Goal _name req _prod) = Subset req avail

type family SelectReady (avail :: [Nat]) (gs :: [Goal]) :: Maybe (Goal, [Goal]) where
  SelectReady _avail '[] = 'Nothing
  SelectReady avail (g ': gs) =
    If (Ready avail g)
      ('Just '(g, gs))
      (SelectReadyCons g (SelectReady avail gs))

type family SelectReadyCons (g :: Goal) (m :: Maybe (Goal, [Goal])) :: Maybe (Goal, [Goal]) where
  SelectReadyCons _ 'Nothing = 'Nothing
  SelectReadyCons g ('Just '(g1, rest)) = 'Just '(g1, g ': rest)

data SolveResult = Solved | Stuck [Nat] [Goal]

type family Solve (avail :: [Nat]) (gs :: [Goal]) :: SolveResult where
  Solve _avail '[] = 'Solved
  Solve avail gs = SolveStep (SelectReady avail gs) avail gs

type family SolveStep (m :: Maybe (Goal, [Goal])) (avail :: [Nat]) (gs :: [Goal]) :: SolveResult where
  SolveStep 'Nothing avail gs = 'Stuck avail gs
  SolveStep ('Just '( 'Goal _name _req prod, rest)) avail _gs = Solve (Union avail prod) rest

type family CheckSchedule (steps :: [Step]) :: Constraint where
  CheckSchedule steps = CheckScheduleResult steps (Solve (ConclVars steps) (PremGoals steps))

type family CheckScheduleResult (steps :: [Step]) (r :: SolveResult) :: Constraint where
  CheckScheduleResult _steps 'Solved = ()
  CheckScheduleResult steps ('Stuck avail gs) =
    TypeError
      ( 'Text "Mode check failed: no runnable premise."
          ':$$: 'Text "  head predicate: " ':<>: 'Text (ConclName steps)
          ':$$: 'Text "  head grounds vars (from I-positions): " ':<>: 'ShowType (ConclVars steps)
          ':$$: 'Text "  stuck with grounded vars: " ':<>: 'ShowType avail
          ':$$: 'Text "  blocked premises:"
          ':$$: ShowBlocked avail gs
          ':$$: 'Text "Hint: every variable used in an I-position must be grounded by the head"
          ':$$: 'Text "      or produced by an O-position of some other premise."
      )

type family Diff (xs :: [Nat]) (ys :: [Nat]) :: [Nat] where
  Diff '[] _ys = '[]
  Diff (x ': xs) ys = If (Elem x ys) (Diff xs ys) (x ': Diff xs ys)

type family ShowBlocked (avail :: [Nat]) (gs :: [Goal]) :: ErrorMessage where
  ShowBlocked _avail '[] = 'Text ""
  ShowBlocked avail ('Goal name req prod ': rest) =
    ( 'Text "    - "
        ':<>: 'Text name
        ':<>: 'Text " requires "
        ':<>: 'ShowType req
        ':<>: 'Text " (missing "
        ':<>: 'ShowType (Diff req avail)
        ':<>: 'Text "), produces "
        ':<>: 'ShowType prod
    )
      ':$$: ShowBlocked avail rest

type family Snoc (xs :: [k]) (x :: k) :: [k] where
  Snoc '[]       x = '[x]
  Snoc (y ': ys) x = y ': Snoc ys x
