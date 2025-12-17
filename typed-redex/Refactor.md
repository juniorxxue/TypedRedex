Comprehensive Library Code Review

  Overview

  The library has a clean conceptual architecture with three main layers:
  1. Core (Logic.hs, Internal/Redex.hs) - type-level foundations
  2. Utils (Redex.hs, Rule.hs, Define.hs, Type.hs, PrettyPrint.hs) - combinators
  3. Interpreters (SubstRedex.hs, TracingRedex.hs, DeepRedex.hs)

  ---
  1. Easy-to-Understand Code

  Issues

  A. Logic.hs has unclear naming and role confusion

  The file mixes several concerns:
  - Logic a var is the main logic term type
  - LogicType is the typeclass for reifiable types
  - Field and Constructor are quotation machinery

  -- Current: name collision with "Logic" module/type
  data Logic a (var :: Type -> Type)
    = Free (Var a var) | Ground (Reified a var)

  Suggestion: Rename to clarify intent:
  - Logic a var → Term a var (matches "logic term" terminology)
  - Or keep Logic but rename module to TypedRedex.Core.Internal.Term

  B. Utils/Redex.hs is a "grab bag" module

  This file contains:
  - fresh, fresh2, ... (variable allocation)
  - relation, relation2, ... (relation construction)
  - run, run2, ... (execution)
  - formatCon, prettyLogic (pretty printing)
  - occursCheck (unification helper)
  - flatteningUnify, evalFromRead (interpreter helpers)

  Suggestion: Split into focused modules:
  Utils/Fresh.hs      - fresh, fresh2, ..., argument, argument2, ...
  Utils/Relation.hs   - relation, relation2, ..., call, premise, embed
  Utils/Run.hs        - run, run2, ..., eval, conde
  Utils/Format.hs     - formatCon, prettyLogic, intercalate

  C. Two competing DSL styles (Rule.hs vs Define.hs)

  Rule.hs:
  stepAppL = rule2 "step-app-l" $ \concl ->
    fresh3 $ \e1 e1' e2 -> do
      concl (app e1 e2) (app e1' e2)
      call (step e1 e1')

  Define.hs:
  stepAppL = rule3 "step-app-l" $ fresh3 $ \e1 e1' e2 -> do
    concl $ step (app e1 e2) (app e1' e2)
    prem  $ step e1 e1'

  Suggestion: Deprecate Rule.hs and keep only Define.hs style. The Define.hs approach is cleaner and matches paper notation better (concl, prem).

  ---
  2. Logic Separation / Layered Logic

  Issues

  A. Circular conceptual dependency between Utils/Redex.hs and interpreters

  Utils/Redex.hs provides:
  - flatteningUnify - used by SubstRedex and TracingRedex
  - occursCheck - used by interpreters
  - prettyLogic - only used by TracingRedex

  But it also provides user-facing functions. This creates confusion about what layer things belong to.

  Suggestion: Create TypedRedex.Core.Internal.Unify for interpreter-shared code:
  -- TypedRedex/Core/Internal/Unify.hs
  module TypedRedex.Core.Internal.Unify
    ( flatteningUnify
    , occursCheck
    , evalFromRead
    ) where

  B. formatCon in Utils/Redex.hs contains domain-specific knowledge

  formatCon "App" [f, a] = "(" ++ f ++ " " ++ a ++ ")"
  formatCon "Lam" [ty, b] = "(λ:" ++ ty ++ ". " ++ b ++ ")"
  formatCon "TVar" [n] = "α" ++ subscriptNum n
  -- ... 30+ special cases

  This is presentation-layer code buried in a utils module, and it has hard-coded knowledge of System F, STLC, etc.

  Suggestion: Move to TypedRedex.Utils.Format and make it customizable:
  -- Default formatting, can be overridden per-example
  data FormatConfig = FormatConfig
    { fcCustom :: String -> [String] -> Maybe String
    , fcDefault :: String -> [String] -> String
    }

  formatCon :: FormatConfig -> String -> [String] -> String
  formatCon cfg name args =
    fromMaybe (fcDefault cfg name args) (fcCustom cfg name args)

  Or simpler: move domain-specific cases to examples, keep only generic formatting in library.

  C. DeepRedex duplicates pretty-printing logic

  DeepRedex.hs has its own prettyL, prettyReified, while Utils/Redex.hs has prettyLogic. Similarly, TracingRedex.hs has prettyResolved.

  Suggestion: Unify into a single parametric pretty-printer in Utils/Format.hs that takes a "how to look up variables" function.

  ---
  3. Naming

  Issues

  A. Inconsistent arity suffixes

  -- Utils/Redex.hs
  fresh, fresh2, fresh3, fresh4, fresh5
  relation, relation2, relation3, relation4, relation5

  -- Utils/Rule.hs
  rule, rule2, rule3, rule4, rule5  -- but no rule1!

  -- Utils/Define.hs
  rule, rule1, rule2, rule3, rule4, rule5  -- has rule1
  judgment, judgment2, judgment3, judgment4, judgment5  -- no judgment1!

  Suggestion: Be consistent. Either always include 1 (rule1, judgment1) or never.

  B. L and Var' type aliases are too terse

  type Var' a rel = Var a (RVar rel)
  type L a rel = Logic a (RVar rel)

  These are heavily used but the names don't convey meaning.

  Suggestion:
  - L a rel → LTerm a rel or LogicTerm a rel
  - Var' a rel → LVar a rel or LogicVar a rel

  C. call vs premise vs embed naming confusion

  call = call_ Opaque    -- with suspension
  premise = call         -- alias for call
  embed = call_ Transparent  -- without suspension

  The premise alias adds no clarity. The embed name is confusing (embed what?).

  Suggestion:
  callGoal = call_ Opaque       -- standard call with fair interleaving
  callDirect = call_ Transparent  -- inline call without suspension
  -- Remove `premise` alias

  D. (===) vs (<=>) operators

  (===) :: L a rel -> Reified a (RVar rel) -> rel ()
  a === b = unify a (Ground b)

  (<=>) :: L a rel -> L a rel -> rel ()
  a <=> b = unify a b

  The asymmetric types are confusing. Why have both?

  Suggestion: Keep only (<=>) for term-term unification. For patterns, clients can use Ground $ project value.

  E. Applied/Applied2/Applied3/... is verbose

  data Applied rel a = Applied { app1Arg :: L a rel, app1Goal :: rel () }
  data Applied2 rel a b = Applied2 { app2Args :: (L a rel, L b rel), app2Goal :: rel () }
  -- etc.

  Suggestion: Use a single GADT with a type-level list:
  data Applied rel (as :: [Type]) where
    Applied1 :: L a rel -> rel () -> Applied rel '[a]
    Applied2 :: L a rel -> L b rel -> rel () -> Applied rel '[a, b]
    -- etc.

  Or simpler: use HList if dependencies allow.

  ---
  4. Code Reuse

  Issues

  A. Boilerplate in arity-indexed families

  fresh, fresh2, fresh3, fresh4, fresh5 are all similar:
  fresh f = fresh_ FreshVar $ f . Free
  fresh2 f = fresh $ \a -> fresh $ \b -> f a b
  fresh3 f = fresh $ \a -> fresh $ \b -> fresh $ \c -> f a b c
  -- etc.

  Same pattern repeats for argument, relation, run, rule, judgment.

  Suggestion: Generate these via type-class based approach or accept the duplication as explicit documentation. Given your "no TH" constraint, a type-class approach would be:

  class FreshN f where
    freshN :: (Redex rel) => f rel -> rel s

  instance (LogicType a) => FreshN (L a rel -> rel s) where
    freshN f = fresh f

  instance (LogicType a, FreshN (f rel)) => FreshN (L a rel -> f rel -> rel s) where
    freshN f = fresh $ \x -> freshN (f x)

  But this may complicate type inference. The explicit approach is probably fine.

  B. SubstRedex and TracingRedex share 80% of code

  Both have:
  - Same Subst/TracingState structure for substitutions
  - Same fresh_ implementation
  - Same unify via flatteningUnify
  - Same derefVar/eval logic

  Suggestion: Extract shared code into an internal module:
  -- TypedRedex/Core/Internal/SubstCore.hs
  -- Contains: Subst type, readSubst, updateSubst, succVar
  -- makeVar, unify implementation, derefVar implementation

  Then SubstRedex and TracingRedex can import and specialize.

  C. formatConclusion duplication in DeepRedex.hs

  DeepRedex.hs has formatConclusion and formatCall with nearly identical case analysis to formatCon in Utils/Redex.hs.

  Suggestion: Unify into one FormatJudgment module that both interpreters use.

  ---
  5. GHC Extension Reduction

  Current extension usage (by frequency):

  | Extension             | Files | Can Remove?                 |
  |-----------------------|-------|-----------------------------|
  | TypeFamilies          | 9     | No - essential for Reified  |
  | Rank2Types/RankNTypes | 7     | No - essential for CPS      |
  | FlexibleContexts      | 6     | No - needed for constraints |
  | MultiParamTypeClasses | 5     | Possibly reduce             |
  | GADTs                 | 4     | No - core to design         |
  | FlexibleInstances     | 4     | Possibly reduce             |
  | UndecidableInstances  | 2     | Maybe reduce                |
  | ImplicitParams        | 1     | Yes - can replace           |
  | ImpredicativeTypes    | 1     | Yes - can refactor          |
  | AllowAmbiguousTypes   | 1     | Maybe reduce                |
  | QuantifiedConstraints | 1     | Likely needed               |

  Actionable reductions:

  A. Remove ImplicitParams from Define.hs

  Current:
  rule3 :: String -> ((?concl :: (L a rel, L b rel, L c rel) -> rel ()) => rel ()) -> Rule3 rel a b c

  Alternative using explicit parameter:
  data RuleEnv3 rel a b c = RuleEnv3
    { conclude3 :: (L a rel, L b rel, L c rel) -> rel () }

  rule3 :: String -> (RuleEnv3 rel a b c -> rel ()) -> Rule3 rel a b c

  Usage changes from concl to conclude3 env but is more explicit.

  Or use ReaderT:
  type RuleM3 rel a b c = ReaderT (Conclude3 rel a b c) rel

  rule3 :: String -> RuleM3 rel a b c () -> Rule3 rel a b c

  B. Remove ImpredicativeTypes

  This is only needed because of:
  data Rule rel a = Rule
    { rule1Name :: String
    , rule1Body :: (?concl :: L a rel -> rel ()) => rel ()
    }

  If you remove ImplicitParams, this goes away.

  C. Reduce ApplicativeDo usage

  Used in Logic.hs and Utils/Redex.hs but often just for sugar. Can replace with explicit <*> chains if cleaner.

  D. Move TypeApplications to call sites only

  DeepRedex.hs uses TypeApplications for varNaming @a. Could use Proxy instead:
  prettyL :: forall a. LogicType a => Proxy a -> Logic a (RVar DeepRedex) -> String
  prettyL _ (Free (DVar n)) = "«" ++ vnTag (varNaming (Proxy @a)) ++ ":" ++ show n ++ "»"

  ---
  Summary of Recommended Changes

  High Priority (Logic Separation & Clarity)

  1. Split Utils/Redex.hs into Fresh.hs, Relation.hs, Run.hs, Format.hs
  2. Move interpreter helpers (flatteningUnify, occursCheck) to Core/Internal/Unify.hs
  3. Extract shared SubstRedex/TracingRedex code into Core/Internal/SubstCore.hs
  4. Deprecate Rule.hs in favor of Define.hs style

  Medium Priority (Naming)

  5. Rename L to LTerm and Var' to LVar
  6. Make arity suffixes consistent (always include 1 or never)
  7. Rename embed to callDirect, remove premise alias
  8. Remove (===), keep only (<=>)

  Lower Priority (Extension Reduction)

  9. Replace ImplicitParams with explicit ReaderT or parameter
  10. Move formatCon domain knowledge to examples

  Optional (Code Reuse)

  11. Unify pretty-printing into single parametric module
  12. Consider if Applied/Rule families can be simplified

  ---
