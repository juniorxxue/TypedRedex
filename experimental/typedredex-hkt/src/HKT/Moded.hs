{-# LANGUAGE TypeFamilies, GADTs, DataKinds, TypeOperators #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, TypeApplications #-}
{-# LANGUAGE UndecidableInstances, AllowAmbiguousTypes #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds, FunctionalDependencies #-}

-- | Mode-guided DSL with compile-time schedule verification.
--
-- = Key Ideas
--
-- 1. Each term carries variable IDs at type level: @T '[0, 2] TyF@
-- 2. Modes declare inputs (I) vs outputs (O)
-- 3. Type-level constraint checks that a valid schedule exists
--
-- = Example
--
-- @
-- typecheck :: MJudgment3 \"check\" (In Env) (In Expr) (Out Ty)
-- typecheck = mjudge3 $ \\rule ->
--   [ rule \"T-Int\" $ R.do
--       gamma <- R.fresh
--       R.concl $ typecheck gamma eint tint
--   ]
-- @
module HKT.Moded
  ( -- * Modes
    Mode(..)
    -- * Moded Terms
  , T(..)
  , ground
    -- * Fresh Variables
  , fresh, fresh2, fresh3, fresh4, fresh5
    -- * Moded Judgments
  , AppliedM(..)
  , MJudgment1, MJudgment2, MJudgment3, MJudgment4
  , mjudge1, mjudge2, mjudge3, mjudge4
    -- * Rule Building
  , RuleM
  , ModedRule(..)
  , ruleM
  , concl, prem
    -- * QualifiedDo
  , return, (>>=), (>>)
    -- * Type-level machinery
  , Union, Subset
  ) where

import Prelude hiding (return, (>>=), (>>))
import qualified Prelude
import Data.Kind (Type, Constraint)
import Data.Proxy (Proxy(..))
import GHC.TypeLits (Symbol, TypeError, ErrorMessage(..), Nat, type (+), KnownSymbol, symbolVal)
import qualified Data.Set as S
import Data.Set (Set)

import HKT.Core

--------------------------------------------------------------------------------
-- Modes
--------------------------------------------------------------------------------

data Mode = I | O

--------------------------------------------------------------------------------
-- Type-level Sets
--------------------------------------------------------------------------------

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

type family If (b :: Bool) (t :: k) (f :: k) :: k where
  If 'True  t _ = t
  If 'False _ f = f

type family And (a :: Bool) (b :: Bool) :: Bool where
  And 'True b = b
  And 'False _ = 'False

type family Diff (xs :: [Nat]) (ys :: [Nat]) :: [Nat] where
  Diff '[] _ = '[]
  Diff (x ': xs) ys = If (Elem x ys) (Diff xs ys) (x ': Diff xs ys)

--------------------------------------------------------------------------------
-- Moded Terms
--------------------------------------------------------------------------------

-- | Term with type-level variable tracking.
--
-- @vs@ tracks which variable IDs this term depends on.
-- @f@ is the base functor (e.g., TyF).
data T (vs :: [Nat]) (f :: Type -> Type) = T
  { tVars :: Set Int      -- ^ Runtime variable IDs
  , tTerm :: Term f       -- ^ The underlying term
  }

-- | Wrap a ground term (no variables).
ground :: Term f -> T '[] f
ground t = T S.empty t

--------------------------------------------------------------------------------
-- Rule State
--------------------------------------------------------------------------------

-- | Steps tracked at type level for schedule checking.
data Goal = Goal Symbol [Nat] [Nat]  -- name, required vars, produced vars
data Step = ConcStep [Nat] [Nat]     -- conclusion: input vars, output vars
          | PremStep Goal

-- | Rule state machine.
data St = St Nat [Step] Bool  -- next var, steps, has conclusion

-- | Premise action for runtime.
data PremAction = PremAction
  { paReq  :: Set Int
  , paProd :: Set Int
  , paGoal :: IO ()  -- placeholder for actual logic
  }

-- | Rule environment during construction.
data RuleEnv = RuleEnv
  { rePrems    :: [PremAction]
  , reAvail    :: Set Int
  , reNextVar  :: Int
  }

-- | Rule monad with type-level state tracking.
newtype RuleM (s :: St) (t :: St) a = RuleM
  { runRuleM :: RuleEnv -> (a, RuleEnv) }

return :: a -> RuleM s s a
return a = RuleM $ \env -> (a, env)

(>>=) :: RuleM s t a -> (a -> RuleM t u b) -> RuleM s u b
RuleM m >>= f = RuleM $ \env ->
  let (a, env') = m env
  in runRuleM (f a) env'

(>>) :: RuleM s t a -> RuleM t u b -> RuleM s u b
m >> k = m >>= \_ -> k

--------------------------------------------------------------------------------
-- Fresh Variables
--------------------------------------------------------------------------------

-- | Create a fresh logic variable.
fresh :: forall f n steps c.
         RuleM ('St n steps c) ('St (n + 1) steps c) (T '[n] f)
fresh = RuleM $ \env ->
  let varId = reNextVar env
  in ( T (S.singleton varId) (Var (VarId varId))
     , env { reNextVar = varId + 1 }
     )

-- | Create 2 fresh variables.
fresh2 :: forall f g n steps c.
          RuleM ('St n steps c) ('St (n + 2) steps c) (T '[n] f, T '[n + 1] g)
fresh2 = RuleM $ \env ->
  let v1 = reNextVar env
      v2 = v1 + 1
  in ( ( T (S.singleton v1) (Var (VarId v1))
       , T (S.singleton v2) (Var (VarId v2))
       )
     , env { reNextVar = v2 + 1 }
     )

-- | Create 3 fresh variables.
fresh3 :: forall f g h n steps c.
          RuleM ('St n steps c) ('St (n + 3) steps c)
            (T '[n] f, T '[n + 1] g, T '[n + 2] h)
fresh3 = RuleM $ \env ->
  let v1 = reNextVar env
      v2 = v1 + 1
      v3 = v2 + 1
  in ( ( T (S.singleton v1) (Var (VarId v1))
       , T (S.singleton v2) (Var (VarId v2))
       , T (S.singleton v3) (Var (VarId v3))
       )
     , env { reNextVar = v3 + 1 }
     )

-- | Create 4 fresh variables.
fresh4 :: forall f g h i n steps c.
          RuleM ('St n steps c) ('St (n + 4) steps c)
            (T '[n] f, T '[n + 1] g, T '[n + 2] h, T '[n + 3] i)
fresh4 = RuleM $ \env ->
  let v1 = reNextVar env
      v2 = v1 + 1
      v3 = v2 + 1
      v4 = v3 + 1
  in ( ( T (S.singleton v1) (Var (VarId v1))
       , T (S.singleton v2) (Var (VarId v2))
       , T (S.singleton v3) (Var (VarId v3))
       , T (S.singleton v4) (Var (VarId v4))
       )
     , env { reNextVar = v4 + 1 }
     )

-- | Create 5 fresh variables.
fresh5 :: forall f g h i j n steps c.
          RuleM ('St n steps c) ('St (n + 5) steps c)
            (T '[n] f, T '[n + 1] g, T '[n + 2] h, T '[n + 3] i, T '[n + 4] j)
fresh5 = RuleM $ \env ->
  let v1 = reNextVar env
      v2 = v1 + 1
      v3 = v2 + 1
      v4 = v3 + 1
      v5 = v4 + 1
  in ( ( T (S.singleton v1) (Var (VarId v1))
       , T (S.singleton v2) (Var (VarId v2))
       , T (S.singleton v3) (Var (VarId v3))
       , T (S.singleton v4) (Var (VarId v4))
       , T (S.singleton v5) (Var (VarId v5))
       )
     , env { reNextVar = v5 + 1 }
     )

--------------------------------------------------------------------------------
-- Mode Analysis
--------------------------------------------------------------------------------

type family ReqVars (modes :: [Mode]) (vss :: [[Nat]]) :: [Nat] where
  ReqVars '[] '[] = '[]
  ReqVars ('I ': ms) (vs ': vss) = Union vs (ReqVars ms vss)
  ReqVars ('O ': ms) (_ ': vss) = ReqVars ms vss

type family ProdVars (modes :: [Mode]) (vss :: [[Nat]]) :: [Nat] where
  ProdVars '[] '[] = '[]
  ProdVars ('I ': ms) (_ ': vss) = ProdVars ms vss
  ProdVars ('O ': ms) (vs ': vss) = Union vs (ProdVars ms vss)

--------------------------------------------------------------------------------
-- Applied Moded Judgment
--------------------------------------------------------------------------------

-- | Result of applying a moded judgment.
data AppliedM (name :: Symbol) (modes :: [Mode]) (vss :: [[Nat]]) = AppliedM
  { amReqVars  :: Set Int
  , amProdVars :: Set Int
  }

--------------------------------------------------------------------------------
-- Conclusion and Premise
--------------------------------------------------------------------------------

type family Snoc (xs :: [k]) (x :: k) :: [k] where
  Snoc '[] x = '[x]
  Snoc (y ': ys) x = y ': Snoc ys x

-- | Declare conclusion.
concl :: forall name modes vss n steps.
         AppliedM name modes vss
      -> RuleM ('St n steps 'False)
               ('St n (Snoc steps ('ConcStep (ReqVars modes vss) (ProdVars modes vss))) 'True)
               ()
concl applied = RuleM $ \env ->
  ((), env { reAvail = amReqVars applied })

-- | Declare premise.
prem :: forall name modes vss n steps c.
        AppliedM name modes vss
     -> RuleM ('St n steps c)
              ('St n (Snoc steps ('PremStep ('Goal name (ReqVars modes vss) (ProdVars modes vss)))) c)
              ()
prem applied = RuleM $ \env ->
  let action = PremAction (amReqVars applied) (amProdVars applied) (Prelude.return ())
  in ((), env { rePrems = action : rePrems env })

--------------------------------------------------------------------------------
-- Schedule Checking
--------------------------------------------------------------------------------

type family ConclVars (steps :: [Step]) :: [Nat] where
  ConclVars ('ConcStep ins _ ': _) = ins
  ConclVars (_ ': rest) = ConclVars rest
  ConclVars '[] = TypeError ('Text "Rule missing conclusion")

type family PremGoals (steps :: [Step]) :: [Goal] where
  PremGoals '[] = '[]
  PremGoals ('PremStep g ': rest) = g ': PremGoals rest
  PremGoals ('ConcStep _ _ ': rest) = PremGoals rest

type family AllPremProds (gs :: [Goal]) :: [Nat] where
  AllPremProds '[] = '[]
  AllPremProds ('Goal _ _ prod ': rest) = Union prod (AllPremProds rest)

type family ConclOutVars (steps :: [Step]) :: [Nat] where
  ConclOutVars ('ConcStep _ outs ': _) = outs
  ConclOutVars (_ ': rest) = ConclOutVars rest
  ConclOutVars '[] = '[]

type family FinalAvail (steps :: [Step]) :: [Nat] where
  FinalAvail steps = Union (ConclVars steps) (AllPremProds (PremGoals steps))

-- Schedule solving
data SolveResult = Solved | Stuck [Nat] [Goal]

type family Ready (avail :: [Nat]) (g :: Goal) :: Bool where
  Ready avail ('Goal _ req _) = Subset req avail

type family SelectReady (avail :: [Nat]) (gs :: [Goal]) :: Maybe (Goal, [Goal]) where
  SelectReady _ '[] = 'Nothing
  SelectReady avail (g ': gs) =
    If (Ready avail g) ('Just '(g, gs)) (PrependMaybe g (SelectReady avail gs))

type family PrependMaybe (g :: Goal) (m :: Maybe (Goal, [Goal])) :: Maybe (Goal, [Goal]) where
  PrependMaybe _ 'Nothing = 'Nothing
  PrependMaybe g ('Just '(g1, rest)) = 'Just '(g1, g ': rest)

type family Solve (avail :: [Nat]) (gs :: [Goal]) :: SolveResult where
  Solve _ '[] = 'Solved
  Solve avail gs = SolveStep (SelectReady avail gs) avail gs

type family SolveStep (m :: Maybe (Goal, [Goal])) (avail :: [Nat]) (gs :: [Goal]) :: SolveResult where
  SolveStep 'Nothing avail gs = 'Stuck avail gs
  SolveStep ('Just '( 'Goal _ _ prod, rest)) avail _ = Solve (Union avail prod) rest

-- Main constraint
type family CheckSchedule (name :: Symbol) (steps :: [Step]) :: Constraint where
  CheckSchedule name steps =
    ( CheckPremises name (Solve (ConclVars steps) (PremGoals steps))
    , CheckOutputs name (ConclOutVars steps) (FinalAvail steps)
    )

type family CheckPremises (name :: Symbol) (r :: SolveResult) :: Constraint where
  CheckPremises _ 'Solved = ()
  CheckPremises name ('Stuck avail gs) = TypeError
    ( 'Text "In rule \"" ':<>: 'Text name ':<>: 'Text "\": cannot schedule premises"
        ':$$: 'Text "  Grounded: " ':<>: 'ShowType avail
        ':$$: 'Text "  Blocked: " ':<>: 'ShowType gs
    )

type family CheckOutputs (name :: Symbol) (outs :: [Nat]) (avail :: [Nat]) :: Constraint where
  CheckOutputs name outs avail =
    If (Subset outs avail) (() :: Constraint)
       (TypeError
         ( 'Text "In rule \"" ':<>: 'Text name ':<>: 'Text "\": outputs not grounded"
             ':$$: 'Text "  Outputs: " ':<>: 'ShowType outs
             ':$$: 'Text "  Available: " ':<>: 'ShowType avail
         ))

--------------------------------------------------------------------------------
-- Moded Rules
--------------------------------------------------------------------------------

-- | A moded rule.
data ModedRule = ModedRule String

-- | Create a rule with compile-time schedule checking.
ruleM :: forall name n steps.
         (KnownSymbol name, CheckSchedule name steps)
      => RuleM ('St 0 '[] 'False) ('St n steps 'True) ()
      -> ModedRule
ruleM body =
  let initEnv = RuleEnv [] S.empty 0
      ((), _finalEnv) = runRuleM body initEnv
  in ModedRule (symbolVal (Proxy @name))

--------------------------------------------------------------------------------
-- Moded Judgment Types
--
-- Note: These work with functors (Type -> Type), not types (Type).
-- E.g., TyF, EnvF, ExprF - not Ty, Env, Expr.
--------------------------------------------------------------------------------

type MJudgment1 (name :: Symbol) (m1 :: Mode) (f1 :: Type -> Type) =
  forall vs1.
    T vs1 f1
    -> AppliedM name '[m1] '[vs1]

type MJudgment2 (name :: Symbol) (m1 :: Mode) (f1 :: Type -> Type)
                                 (m2 :: Mode) (f2 :: Type -> Type) =
  forall vs1 vs2.
    T vs1 f1 -> T vs2 f2
    -> AppliedM name '[m1, m2] '[vs1, vs2]

type MJudgment3 (name :: Symbol) (m1 :: Mode) (f1 :: Type -> Type)
                                 (m2 :: Mode) (f2 :: Type -> Type)
                                 (m3 :: Mode) (f3 :: Type -> Type) =
  forall vs1 vs2 vs3.
    T vs1 f1 -> T vs2 f2 -> T vs3 f3
    -> AppliedM name '[m1, m2, m3] '[vs1, vs2, vs3]

type MJudgment4 (name :: Symbol) (m1 :: Mode) (f1 :: Type -> Type)
                                 (m2 :: Mode) (f2 :: Type -> Type)
                                 (m3 :: Mode) (f3 :: Type -> Type)
                                 (m4 :: Mode) (f4 :: Type -> Type) =
  forall vs1 vs2 vs3 vs4.
    T vs1 f1 -> T vs2 f2 -> T vs3 f3 -> T vs4 f4
    -> AppliedM name '[m1, m2, m3, m4] '[vs1, vs2, vs3, vs4]

--------------------------------------------------------------------------------
-- Judgment Constructors
--------------------------------------------------------------------------------

class InputVars (ms :: [Mode]) (vss :: [[Nat]]) where
  inputVars :: [Set Int] -> Set Int

instance InputVars '[] '[] where
  inputVars [] = S.empty
  inputVars _ = error "impossible"

instance InputVars ms vss => InputVars ('I ': ms) (vs ': vss) where
  inputVars (v:vs) = S.union v (inputVars @ms @vss vs)
  inputVars [] = error "impossible"

instance InputVars ms vss => InputVars ('O ': ms) (vs ': vss) where
  inputVars (_:vs) = inputVars @ms @vss vs
  inputVars [] = error "impossible"

class OutputVars (ms :: [Mode]) (vss :: [[Nat]]) where
  outputVars :: [Set Int] -> Set Int

instance OutputVars '[] '[] where
  outputVars [] = S.empty
  outputVars _ = error "impossible"

instance OutputVars ms vss => OutputVars ('I ': ms) (vs ': vss) where
  outputVars (_:vs) = outputVars @ms @vss vs
  outputVars [] = error "impossible"

instance OutputVars ms vss => OutputVars ('O ': ms) (vs ': vss) where
  outputVars (v:vs) = S.union v (outputVars @ms @vss vs)
  outputVars [] = error "impossible"

mjudge1 :: forall name m1 f1.
           (InputVars '[m1] '[ '[]], OutputVars '[m1] '[ '[]])
        => [ModedRule]
        -> MJudgment1 name m1 f1
mjudge1 _rules (T v1 _) = AppliedM
  { amReqVars = inputVars @'[m1] @'[ '[]] [v1]
  , amProdVars = outputVars @'[m1] @'[ '[]] [v1]
  }

mjudge2 :: forall name m1 f1 m2 f2 vs1 vs2.
           (InputVars '[m1, m2] '[vs1, vs2],
            OutputVars '[m1, m2] '[vs1, vs2])
        => [ModedRule]
        -> T vs1 f1 -> T vs2 f2
        -> AppliedM name '[m1, m2] '[vs1, vs2]
mjudge2 _rules (T v1 _) (T v2 _) = AppliedM
  { amReqVars = inputVars @'[m1, m2] @'[vs1, vs2] [v1, v2]
  , amProdVars = outputVars @'[m1, m2] @'[vs1, vs2] [v1, v2]
  }

mjudge3 :: forall name m1 f1 m2 f2 m3 f3 vs1 vs2 vs3.
           (InputVars '[m1, m2, m3] '[vs1, vs2, vs3],
            OutputVars '[m1, m2, m3] '[vs1, vs2, vs3])
        => [ModedRule]
        -> T vs1 f1 -> T vs2 f2 -> T vs3 f3
        -> AppliedM name '[m1, m2, m3] '[vs1, vs2, vs3]
mjudge3 _rules (T v1 _) (T v2 _) (T v3 _) = AppliedM
  { amReqVars = inputVars @'[m1, m2, m3] @'[vs1, vs2, vs3] [v1, v2, v3]
  , amProdVars = outputVars @'[m1, m2, m3] @'[vs1, vs2, vs3] [v1, v2, v3]
  }

mjudge4 :: forall name m1 f1 m2 f2 m3 f3 m4 f4 vs1 vs2 vs3 vs4.
           (InputVars '[m1, m2, m3, m4] '[vs1, vs2, vs3, vs4],
            OutputVars '[m1, m2, m3, m4] '[vs1, vs2, vs3, vs4])
        => [ModedRule]
        -> T vs1 f1 -> T vs2 f2 -> T vs3 f3 -> T vs4 f4
        -> AppliedM name '[m1, m2, m3, m4] '[vs1, vs2, vs3, vs4]
mjudge4 _rules (T v1 _) (T v2 _) (T v3 _) (T v4 _) = AppliedM
  { amReqVars = inputVars @'[m1, m2, m3, m4] @'[vs1, vs2, vs3, vs4] [v1, v2, v3, v4]
  , amProdVars = outputVars @'[m1, m2, m3, m4] @'[vs1, vs2, vs3, vs4] [v1, v2, v3, v4]
  }
