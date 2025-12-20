# Mode-Guided Static Scheduling for TypedRedex

## Technical Proposal

### Motivation

Currently, TypedRedex rules execute premises in source order. This creates two problems:

1. **User burden**: Users must manually order premises so inputs are bound before use
2. **Silent failures**: Wrong ordering leads to runtime divergence or incorrect results, with no compile-time feedback

The solution: **statically-checked mode annotations** that:
- Declare which positions are inputs (I) vs outputs (O)
- Verify at compile time that a valid execution schedule exists
- Generate efficient runtime scheduling based on modes

### Demo Analysis: `examples/mode-indexed/IndexedRule.hs`

The demo proves the core idea works. Key observations:

1. **Type-level variable tracking** (`Term vs`) tracks which fresh variables appear in a term
2. **Mode-based requirements** (`ReqVars`, `ProdVars`) compute which vars are needed/produced
3. **Compile-time scheduling** (`CheckSchedule`, `Solve`) verifies a valid schedule exists
4. **Atkey-style indexed monad** (`RuleM s t a`) tracks state transitions at the type level

Example from the demo:
```haskell
good = rule $ R.do
    x <- fresh
    y <- fresh
    prem (q y)      -- q requires y
    prem (p x y)    -- p requires x, produces y
    concl (h x)     -- concl grounds x
-- Compiles! Schedule: concl → p → q
```

### Architecture Overview

```
┌────────────────────────────────────────────────────────────────┐
│  User-Facing DSL (minimal changes from current syntax)        │
│    judgmentM @"typeof" (I :* I :* O :* MNil) [rule1, rule2]   │
│    ruleM "name" $ R.do { fresh; prem; concl }                 │
├────────────────────────────────────────────────────────────────┤
│  TypedRedex.DSL.Moded  (NEW)                                  │
│    - ModeList, Mode data types                                │
│    - RuleM indexed monad (Atkey-style)                        │
│    - fresh, prem, concl with var-set tracking                 │
│    - Type-level scheduling verification (CheckSchedule)       │
├────────────────────────────────────────────────────────────────┤
│  TypedRedex.DSL.Moded.Term  (NEW)                             │
│    - T vs a rel: term wrapper with type-level var set         │
│    - Lifted constructors via lift1/lift2/lift3                │
├────────────────────────────────────────────────────────────────┤
│  TypedRedex.Core.Internal.Walk  (NEW)                         │
│    - RedexWalk class: isGround, walkL for runtime checks      │
├────────────────────────────────────────────────────────────────┤
│  TypedRedex.Core.Internal.Schedule  (NEW)                     │
│    - Runtime scheduler: execute plan based on readiness       │
├────────────────────────────────────────────────────────────────┤
│  Existing Core (Redex, Logic, Relation, etc.)                 │
│    - Unchanged, scheduler generates rel () goals              │
└────────────────────────────────────────────────────────────────┘
```

---

## Step-by-Step Migration Plan

### Phase 1: Core Infrastructure (Foundation)

#### Step 1: Promote Demo to Library Module

**Files to create:**
- `src/TypedRedex/DSL/Moded.hs`

**What to do:**
1. Copy `IndexedRule.hs` into `src/TypedRedex/DSL/Moded.hs`
2. Rename module to `TypedRedex.DSL.Moded`
3. Add export from `TypedRedex.hs`:
   ```haskell
   -- Moded DSL (experimental)
   import TypedRedex.DSL.Moded (...)
   ```

**Key changes from demo:**
- Replace phantom `Term vs` with actual `LTerm` integration
- Keep all type-level machinery (`ReqVars`, `ProdVars`, `Solve`, etc.)

#### Step 2: Type-Level Judgment Names (Better Error Messages)

**Goal:** Mode errors should report which judgment/rule failed.

**Current:**
```haskell
judgment "typeof" [rule1, rule2]
```

**Target:**
```haskell
judgmentM @"typeof" modes [rule1, rule2]
-- Error: Mode check failed in judgment "typeof": ...
```

**Implementation:**
```haskell
{-# LANGUAGE TypeApplications, DataKinds #-}

judgmentM :: forall (name :: Symbol) rel ts modes.
  ( KnownSymbol name
  , BuildLTermList rel ts
  , ...
  ) => ModeList modes -> [RuleM name modes rel ts] -> Judge rel ts
```

#### Step 3: Introduce `JudgeM` Type

**Goal:** Encode judgment name and modes in the type for static checking.

```haskell
-- Current type alias
type Judge rel ts = CurriedR rel ts (Applied rel ts)

-- New type with name/modes
data JudgeM (name :: Symbol) (modes :: [Mode]) rel (ts :: [Type]) = JudgeM
  { judgeApplied :: Curried rel ts
  }
```

This enables:
- Mode checking across premise calls
- Meaningful error messages with predicate names

---

### Phase 2: Indexed Rule DSL

#### Step 4: Build Rule Plans (Not Immediate Execution)

**Current behavior:** `prem` and `concl` execute immediately.

**New behavior:** Build a typed plan, execute later.

**RuleM indexed monad:**
```haskell
-- State tracks: fresh var counter, recorded steps, whether concl seen
data St = St Nat [Step] Bool

data Step
  = Concl Symbol [Nat]           -- head pattern grounds these vars
  | Prem (Goal Symbol [Nat] [Nat])  -- prem requires/produces vars

newtype RuleM (name :: Symbol) (modes :: [Mode]) (s :: St) (t :: St) a = RuleM
  { unRuleM :: ... actual computation ... }
```

**Key operations:**
```haskell
fresh :: RuleM name modes
         ('St n steps c)
         ('St (n+1) steps c)
         (T '[n] a rel)

prem :: Applied name' modes' rel ts'
     -> RuleM name modes
          ('St n steps c)
          ('St n (steps :++ '[Prem goal]) c)
          ()

concl :: Applied name modes rel ts
      -> RuleM name modes
           ('St n steps 'False)
           ('St n (steps :++ '[Concl ...]) 'True)
           ()
```

#### Step 5: Compile-Time Mode Checking

**Port from demo** with improvements:

```haskell
type family CheckSchedule (name :: Symbol) (steps :: [Step]) :: Constraint where
  CheckSchedule name steps =
    CheckScheduleResult name steps (Solve (ConclVars steps) (PremGoals steps))

type family CheckScheduleResult (name :: Symbol) (steps :: [Step]) (r :: SolveResult)
    :: Constraint where
  CheckScheduleResult _name _steps 'Solved = ()
  CheckScheduleResult name steps ('Stuck avail gs) =
    TypeError
      ( 'Text "Mode check failed in rule for \""
          ':<>: 'Text name ':<>: 'Text "\":"
          ':$$: 'Text "  head grounds vars: " ':<>: 'ShowType (ConclVars steps)
          ':$$: 'Text "  stuck with: " ':<>: 'ShowType avail
          ':$$: 'Text "  blocked premises:"
          ':$$: ShowBlocked avail gs
          ':$$: 'Text ""
          ':$$: 'Text "Hint: ensure every I-position var is grounded by head"
          ':$$: 'Text "      or produced (O-position) by some premise."
      )
```

---

### Phase 3: Term Wrapper & Syntax Lifting

#### Step 6: Staged Term Wrapper (`T vs a rel`)

**Goal:** Track which fresh variables appear in each term.

```haskell
-- Wrapper that carries type-level var set
newtype T (vs :: [Nat]) (a :: Type) (rel :: Type -> Type) = T
  { unT :: LTerm a rel }

-- Fresh allocation records the var
fresh :: RuleM name modes
         ('St n steps c)
         ('St (n+1) steps c)
         (T '[n] a rel)
fresh = RuleM $ \st -> (T (Free freshVar), incrCounter st)
```

**Lifting syntax constructors:**
```haskell
-- Generic lifters
lift0 :: LTerm a rel -> T '[] a rel
lift0 = T

lift1 :: (LTerm a rel -> LTerm b rel)
      -> T vs a rel -> T vs b rel
lift1 f (T x) = T (f x)

lift2 :: (LTerm a rel -> LTerm b rel -> LTerm c rel)
      -> T vs1 a rel -> T vs2 b rel -> T (Union vs1 vs2) c rel
lift2 f (T x) (T y) = T (f x y)
```

**Per-language lifting (in Syntax.hs):**
```haskell
-- In examples/stlc-bidir/Main.hs (or a Syntax module)
lamM :: T vs (LTerm Tm rel) -> T vs (LTerm Tm rel)
lamM = lift1 lam

appM :: T vs1 (LTerm Tm rel) -> T vs2 (LTerm Tm rel) -> T (Union vs1 vs2) (LTerm Tm rel)
appM = lift2 app
```

---

### Phase 4: Runtime Scheduling

#### Step 7: Runtime Scheduler

**Interpretation strategy:**
1. Always run head unification first (from `concl`)
2. Repeatedly pick a runnable premise using readiness checks
3. Execute premises in computed order

```haskell
-- Recorded rule plan
data RulePlan rel ts = RulePlan
  { planConcl :: LTermList rel ts -> rel ()  -- head unification
  , planPrems :: [RuntimePrem rel]           -- premises with readiness info
  }

data RuntimePrem rel = RuntimePrem
  { premModes :: [Mode]           -- declared modes
  , premArgs  :: [SomeArg rel]    -- actual arguments
  , premGoal  :: rel ()           -- the goal to run
  }

-- Execute plan with mode-guided scheduling
executePlan :: Redex rel => RulePlan rel ts -> LTermList rel ts -> rel ()
executePlan plan args = do
  planConcl plan args    -- unify head first
  runPrems (planPrems plan)

runPrems :: (Redex rel, RedexWalk rel) => [RuntimePrem rel] -> rel ()
runPrems [] = pure ()
runPrems prems = do
  -- Find first premise where all I-positions are bound
  case findReady prems of
    Nothing -> error "No runnable premise (should not happen if mode check passed)"
    Just (ready, rest) -> do
      premGoal ready
      runPrems rest

findReady :: RedexWalk rel => [RuntimePrem rel] -> Maybe (RuntimePrem rel, [RuntimePrem rel])
findReady prems = ... -- check isBound for I-positions
```

#### Step 8: `RedexWalk` Class for Introspection

**Factor out from Subst/Tracing into shared class:**

```haskell
-- src/TypedRedex/Core/Internal/Walk.hs
class Redex rel => RedexWalk rel where
  -- Check if a term is fully ground (no Free vars)
  isGroundL :: LogicType a => Logic a (RVar rel) -> rel Bool

  -- Check if a term is "bound enough" (root is not Free)
  isBoundL :: LogicType a => Logic a (RVar rel) -> rel Bool

  -- Walk/dereference without forcing full resolution
  walkL :: LogicType a => Logic a (RVar rel) -> rel (Logic a (RVar rel))
```

**Implementation in SubstRedex:**
```haskell
instance RedexWalk SubstRedex where
  walkL (Free v) = do
    subst <- getSubst
    case lookupVar v subst of
      Nothing -> pure (Free v)
      Just t  -> walkL t
  walkL t = pure t

  isBoundL t = do
    t' <- walkL t
    case t' of
      Free _ -> pure False
      _      -> pure True
```

---

### Phase 5: Primitives & Integration

#### Step 9: Wrap Non-Relational Helpers as Primitives

**Problem:** Functions like `instantiateTo` need to participate in scheduling.

**Solution:** Wrap as primitive judgments with modes:

```haskell
-- Declare a primitive with modes
primitiveM :: forall (name :: Symbol) modes rel.
  KnownSymbol name =>
  ModeList modes ->
  (args... -> rel ()) ->
  ... moded judgment type ...

-- Usage
instantiateToM :: JudgeM "instantiateTo" '[GI, GI, O] rel '[Ty, Nat, Ty]
instantiateToM = primitiveM @"instantiateTo" (GI :* GI :* O :* MNil) instantiateTo
```

**Mode `GI` (Ground Input):** Must be fully ground before running.

---

### Phase 6: Incremental Migration

#### Step 10: Migrate Judgments One at a Time

**Migration checklist per judgment:**

1. Add language extensions:
   ```haskell
   {-# LANGUAGE QualifiedDo, DataKinds, TypeApplications #-}
   ```

2. Change judgment definition:
   ```haskell
   -- Before
   lookup' :: Redex rel => Judge rel '[Ctx, Nat, Ty]
   lookup' = judgment "lookup" [lookupHere, lookupThere]

   -- After
   lookup' :: Redex rel => JudgeM "lookup" '[I, I, O] rel '[Ctx, Nat, Ty]
   lookup' = judgmentM @"lookup" (I :* I :* O :* MNil) [lookupHere, lookupThere]
   ```

3. Change rule bodies to indexed monad:
   ```haskell
   -- Before
   lookupHere = rule "lookup-here" $ fresh2 $ \ty rest ->
     concl $ lookup' (cons ty rest) zro ty

   -- After
   import qualified TypedRedex.DSL.Moded as R

   lookupHere = ruleM "lookup-here" $ R.do
     ty <- fresh
     rest <- fresh
     concl $ lookup' (consM ty rest) zroM ty
   ```

4. Fix mode errors by adjusting modes or adding producing premises

**Migration order (suggested):**
1. `lookup` (simple, I/I/O pattern)
2. `value` (unary predicate, just I)
3. `synth` / `check` (standard bidir pattern)
4. `step` (complex, may need scheduler)

---

## Target End-State (User-Facing)

### Syntax Comparison

**Current:**
```haskell
typeof :: Redex rel => Judge rel '[Ctx, Tm, Ty]
typeof = judgment "typeof" [typeofVar, typeofLam, typeofApp]
  where
    typeofApp = rule "typeof-app" $ fresh5 $ \ctx e1 e2 a b -> do
      concl $ typeof ctx (app e1 e2) b
      prem  $ typeof ctx e1 (tarr a b)
      prem  $ typeof ctx e2 a
```

**After migration:**
```haskell
import qualified TypedRedex.DSL.Moded as R

typeof :: Redex rel => JudgeM "typeof" '[I, I, O] rel '[Ctx, Tm, Ty]
typeof = judgmentM @"typeof" (I :* I :* O :* MNil) [typeofVar, typeofLam, typeofApp]
  where
    typeofApp = ruleM "typeof-app" $ R.do
      ctx <- fresh
      e1 <- fresh; e2 <- fresh
      a <- fresh; b <- fresh
      prem  $ typeof ctx e2 a           -- Order doesn't matter!
      concl $ typeof ctx (appM e1 e2) b -- Scheduler finds valid order
      prem  $ typeof ctx e1 (tarrM a b)
```

**Benefits:**
- Premises in any order (scheduler reorders)
- Compile-time rejection of ill-moded rules
- Clear mode documentation in types

---

## Alternative: `RebindableSyntax` Instead of `QualifiedDo`

**Note:** Using `{-# LANGUAGE RebindableSyntax #-}` can avoid `R.do` prefix:

```haskell
{-# LANGUAGE RebindableSyntax #-}
import TypedRedex.DSL.Moded (return, (>>=), (>>), fail, ...)
import Prelude hiding (return, (>>=), (>>), fail, ...)

-- Now plain do-notation uses the indexed monad
typeofApp = ruleM "typeof-app" $ do
  ctx <- fresh
  ...
```

**Trade-offs:**
- Pro: Cleaner syntax, no `R.do` prefix
- Con: Affects entire module, may conflict with other monads
- Con: More invasive change for users

**Recommendation:** Start with `QualifiedDo`, offer `RebindableSyntax` as optional style.

---

## Dependencies & Prerequisites

### New GHC Extensions Required
- `DataKinds` (already used in demo)
- `TypeFamilies` (already used)
- `QualifiedDo` or `RebindableSyntax`
- `TypeApplications` (for `@"name"` syntax)
- `UndecidableInstances` (for type-level computation)

### New Modules to Create
1. `TypedRedex.DSL.Moded` - Core indexed monad and mode DSL
2. `TypedRedex.DSL.Moded.Term` - Term wrapper with var tracking
3. `TypedRedex.Core.Internal.Walk` - Introspection class
4. `TypedRedex.Core.Internal.Schedule` - Runtime scheduler

### Files to Modify
1. `TypedRedex.hs` - Export new moded API
2. `TypedRedex.DSL.Define.hs` - Keep for backwards compat, deprecate later
3. Each example's `Syntax.hs` - Add lifted constructors

---

## Risks & Mitigations

| Risk | Mitigation |
|------|------------|
| Type errors too complex | Invest in `TypeError` messages; test with real users |
| Compile-time overhead | Profile; consider staged type families if needed |
| Breaking existing code | Keep old API, migrate incrementally, use deprecation warnings |
| Runtime scheduler overhead | Benchmark; scheduler runs once per rule, should be minimal |
| Lifted syntax boilerplate | Provide TH or Generic deriving for lifters |



> any literature or software or language uses similar technique? I need references

⏺ Good question. Mode systems for logic programming are well-established. Here are the key references:

  Primary References

  Mercury (The Gold Standard)

  Mercury is the canonical example of a logic/functional language with static mode checking.

  - Somogyi, Henderson, Conway (1996) — "The Execution Algorithm of Mercury: An Efficient Purely Declarative Logic Programming Language" — JLP 29(1-3).
    - Core paper describing Mercury's mode system and determinism inference.
  - Somogyi, Henderson, Conway (1995) — "Mercury: An Efficient Purely Declarative Logic Programming Language" — Australian Computer Science Conference.
  - Mercury Language Reference — https://mercurylang.org/information/doc-release/mercury_ref/Modes.html
    - Documents in, out, di, uo (unique output) modes.

  Twelf (Modes for LF)

  Twelf uses modes for termination and coverage checking of logic programs over LF.

  - Rohwedder & Pfenning (1996) — "Mode and Termination Checking for Higher-Order Logic Programs" — ESOP'96.
    - Mode checking ensures inputs are ground before use.
  - Twelf User's Guide, Section 6: Mode Checking — http://twelf.org/wiki/Mode_checking

  Prolog Mode Analysis (Abstract Interpretation)

  - Debray & Warren (1988) — "Automatic Mode Inference for Logic Programs" — JLP 5(3).
    - Infers modes via abstract interpretation rather than declarations.
  - Bruynooghe (1991) — "A Practical Framework for the Abstract Interpretation of Logic Programs" — JLP 10(2).
  - Van Hentenryck, Cortesi, Le Charlier (1995) — "Evaluation of the Domain Prop" — JLP 23(3).

  Indexed/Graded Monads (The RuleM Technique)

  The Atkey-style indexed monad used in the demo:

  - Atkey (2009) — "Parameterised Notions of Computation" — JFP 19(3-4).
    - Foundational paper on indexed monads.
  - McBride (2011) — "Kleisli Arrows of Outrageous Fortune" — unpublished note.
    - Accessible introduction to indexed monads for effect tracking.

  Type-Level Programming in Haskell

  For the compile-time scheduling verification technique:

  - Eisenberg & Weirich (2012) — "Dependently Typed Programming with Singletons" — Haskell Symposium.
  - Lindley & McBride (2013) — "Hasochism: The Pleasure and Pain of Dependently Typed Haskell Programming" — Haskell Symposium.

  ---
  Software Systems

  | System           | Mode Support          | Notes                                      |
  |------------------|-----------------------|--------------------------------------------|
  | Mercury          | Static, mandatory     | Most sophisticated; determinism categories |
  | Twelf            | Static, mandatory     | For LF; ensures termination                |
  | Ciao Prolog      | Optional assertions   | pred foo(+In, -Out) syntax                 |
  | SWI-Prolog       | Optional declarations | mode/1 for documentation/analysis          |
  | λProlog (Teyjus) | Limited               | Some mode-like restrictions                |
  | Curry            | Narrowing-based       | Different approach (residuation)           |

  ---
  Specific Techniques in Your Design

  | Your Technique                | Prior Art                            |
  |-------------------------------|--------------------------------------|
  | Type-level var sets (Term vs) | Dependent types / indexed types      |
  | I/O/GI modes                  | Mercury's in/out/ground              |
  | Compile-time schedule check   | Mercury's mode checker, Twelf        |
  | Runtime readiness check       | Residuation in Curry, delay in Gödel |
  | Atkey-indexed RuleM           | Graded/indexed monads literature     |

  ---
  Suggested Citations for a Paper

  @article{somogyi1996mercury,
    title={The execution algorithm of {Mercury}, an efficient purely
           declarative logic programming language},
    author={Somogyi, Zoltan and Henderson, Fergus and Conway, Thomas},
    journal={Journal of Logic Programming},
    volume={29},
    number={1-3},
    pages={17--64},
    year={1996}
  }

  @inproceedings{rohwedder1996mode,
    title={Mode and termination checking for higher-order logic programs},
    author={Rohwedder, Ekkehard and Pfenning, Frank},
    booktitle={European Symposium on Programming (ESOP)},
    pages={296--310},
    year={1996},
    publisher={Springer}
  }

  @article{atkey2009parameterised,
    title={Parameterised notions of computation},
    author={Atkey, Robert},
    journal={Journal of Functional Programming},
    volume={19},
    number={3-4},
    pages={335--376},
    year={2009}
  }

  @article{debray1988modes,
    title={Automatic mode inference for logic programs},
    author={Debray, Saumya K and Warren, David S},
    journal={Journal of Logic Programming},
    volume={5},
    number={3},
    pages={207--229},
    year={1988}
  }

  ---
  Key Distinction (Novelty Angle)

  Most prior work either:
  1. Mercury/Twelf: Modes are checked but scheduling is fixed (left-to-right)
  2. Ciao/SWI: Modes are assertions, not enforced statically

  Your approach combines:
  - Static verification (like Mercury/Twelf) that a schedule exists
  - Dynamic scheduling (like residuation/delay) that picks order at runtime
  - Embedded in Haskell via indexed monads (novel realization)

  This "statically verified, dynamically scheduled" combination is the distinguishing feature worth highlighting.
