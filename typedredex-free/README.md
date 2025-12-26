# typedredex-free

An alternative DSL layer for TypedRedex using **indexed free monads**.

## Overview

This package provides the same user-facing API as `typedredex-dsl` but uses an **indexed free monad** to represent rule bodies as pure ASTs. This enables complete separation of syntax and semantics, allowing the same rule definition to be interpreted multiple ways.

## Quick Comparison

```haskell
-- typedredex-dsl (current)
rule "lookup-here" $ do    -- do-block runs in StateT over rel
    (ty, rest) <- fresh2   -- fresh_ executes in rel NOW
    concl $ ...            -- unifyLList executes NOW
    prem $ ...             -- collected in reDeferred

-- typedredex-free (this package)
rule "lookup-here" $ do    -- do-block builds IxFree AST
    (ty, rest) <- fresh2   -- creates FreshF node
    concl $ ...            -- creates ConclF node
    prem $ ...             -- creates PremF node
-- Nothing executes until interpretation!
```

## Architecture

```
          IxFree (RuleF rel ts) s t a
                     │
                     │ Pure AST
                     │
    ┌────────────────┼────────────────┐
    │                │                │
    ▼                ▼                ▼
  Eval           Typeset          Trace
(execute)    (extract rules)  (derivation trees)
```

## Key Types

### Indexed Free Monad

```haskell
-- IxFree f i j a: free monad with state transition i → j
data IxFree (f :: k -> k -> Type -> Type) (i :: k) (j :: k) (a :: Type) where
  Pure :: a -> IxFree f i i a                          -- identity transition
  Bind :: f i m x -> (x -> IxFree f m j a) -> IxFree f i j a  -- chained transition
```

### Rule State

```haskell
-- State tracks: (nextVar, steps, hasConclusion)
data St = St Nat [Step] Bool

-- Steps accumulate for compile-time analysis
data Step
  = ConcStep Symbol [Nat] [Nat]   -- conclusion: name, inputs, outputs
  | PremStep Goal                 -- premise
  | NegStep [Nat]                 -- negation: required vars
```

### Indexed Functor

```haskell
data RuleF (rel :: Type -> Type) (ts :: [Type]) (s :: St) (t :: St) (a :: Type) where
  FreshF :: LogicType a
         => RuleF rel ts ('St n steps c) ('St (n+1) steps c) (T '[n] a rel)

  ConclF :: AppliedM rel name modes vss ts
         -> RuleF rel ts ('St n steps 'False) ('St n steps' 'True) ()

  PremF :: AppliedM rel name modes vss ts'
        -> RuleF rel ts ('St n steps c) ('St n steps' c) ()
```

## Motivation

### 1. Complete Separation of Syntax and Semantics

With the current `typedredex-dsl`, rule bodies are hybrid: `concl` executes immediately while `prem`/`neg` are deferred. This makes certain transformations difficult.

With indexed free monads, the **entire rule body is pure data**:

```haskell
-- This builds a data structure, nothing executes
myRule :: IxFree (RuleF rel ts) ('St 0 '[] 'False) ('St n steps 'True) ()
myRule = do
  x <- fresh
  concl $ foo x
  prem $ bar x

-- We can inspect, transform, or optimize before interpretation
analyze myRule  -- count variables, check patterns
transform myRule  -- rewrite rules
interpret myRule  -- finally execute
```

### 2. Multiple Interpreters for Same AST

```haskell
-- Same rule definition, three different interpretations:
interpretEval myRule     -- Execute via substitution
interpretTypeset myRule  -- Extract as ASCII inference rule
interpretTrace myRule    -- Build derivation tree
```

### 3. First-Class Rules

Rules become data that can be:
- Stored in collections
- Passed to higher-order functions
- Serialized/deserialized
- Compared for equality
- Optimized via transformations

### 4. Better Testability

```haskell
-- Test rule structure without execution
testRule = do
  let ast = buildRule myRule
  assertEqual (countFresh ast) 3
  assertEqual (hasConcl ast) True
  assertEqual (countPrem ast) 2
```

## Comparison with typedredex-dsl

| Aspect | typedredex-dsl | typedredex-free |
|--------|---------------|-----------------|
| **Do-notation produces** | State computation over `rel` | Pure `IxFree` AST |
| **`fresh`** | Executes `fresh_` in `rel` now | Creates `FreshF` node |
| **`concl`** | Executes unification now | Creates `ConclF` node |
| **`prem`/`neg`** | Collected as `DeferredAction` | Creates `PremF`/`NegF` nodes |
| **The "AST"** | Partial (`reDeferred` list) | Complete (`IxFree` tree) |
| **Execution** | Hybrid (some now, some later) | All during interpretation |
| **Mode checking** | ✓ Compile-time | ✓ Compile-time (same!) |
| **Performance** | Slightly faster (less allocation) | More allocation |
| **Flexibility** | Limited | High |

## Pros

1. **Purer Separation**: Complete separation of rule definition and execution
2. **Multiple Interpretations**: Same AST, different semantics
3. **Better for Transformations**: Easy to add optimization passes
4. **Easier Testing**: Inspect AST structure without execution
5. **Clearer Mental Model**: Everything is data until interpretation
6. **Algebraic Properties**: Free monads have well-understood laws

## Cons

1. **More Allocation**: Intermediate `IxFree` data structure
2. **Complexity**: Indexed types add cognitive overhead
3. **Performance**: Slightly slower than direct execution
4. **Loss of Immediate Feedback**: `concl` doesn't fail-fast anymore

## Challenges Encountered

### 1. Indexed Type Complexity

The type-level state tracking requires careful management:

```haskell
-- Each operation must correctly specify state transitions
FreshF :: RuleF rel ts ('St n steps c) ('St (n+1) steps c) ...
                        ^^^^^^^^^^^^^^   ^^^^^^^^^^^^^^^^
                        input state      output state
```

### 2. Type-Level List Accumulation

The `steps` list grows at the type level through `Snoc`:

```haskell
type family Snoc (xs :: [k]) (x :: k) :: [k] where
  Snoc '[] x = '[x]
  Snoc (y ': ys) x = y ': Snoc ys x
```

This is necessary for `CheckSchedule` to see all operations.

### 3. QualifiedDo Integration

Indexed monads require custom bind:

```haskell
(>>=) :: IxFree f i j a -> (a -> IxFree f j k b) -> IxFree f i k b
--                  ^                  ^
--                  └── must match ────┘
```

QualifiedDo makes this ergonomic.

### 4. Preserving Compile-Time Checking

The key insight: `CheckSchedule` operates on the **type-level `steps` list**, which accumulates identically in both approaches. The free monad structure is orthogonal to when type checking happens.

## Novelties

### 1. Indexed Free Monad for Logic DSL

To our knowledge, this is the first use of indexed free monads for a mode-checked logic programming DSL.

### 2. Type-Level Schedule Verification with Free

We demonstrate that compile-time mode checking via type families works seamlessly with free monad ASTs.

### 3. Unified Multi-Interpretation

The same rule definition serves for:
- Execution (eval)
- Documentation (typeset)
- Debugging (trace)

## Usage

```haskell
{-# LANGUAGE QualifiedDo, DataKinds, TypeApplications #-}
import qualified TypedRedex.Free as R

lookupCtx :: R.Judgment3 rel "lookup" '[R.I, R.I, R.O] Ctx Nat Ty
lookupCtx = R.defJudge3 @"lookup" $ \rule ->
  [ rule "lookup-here" $ R.do
      (ty, rest) <- R.fresh2
      R.concl $ lookupCtx (cons ty rest) zro ty

  , rule "lookup-there" $ R.do
      (ty', rest, n', ty) <- R.fresh4
      R.concl $ lookupCtx (cons ty' rest) (suc n') ty
      R.prem  $ lookupCtx rest n' ty
  ]
```

## Future Work

1. **Church Encoding**: Use Church-encoded free for better performance
2. **Effect Handlers**: Integration with modern effect systems
3. **Rule Optimization**: AST-level rule transformations
4. **Partial Evaluation**: Specialize rules for specific patterns
5. **Nominal Binding**: Full integration with nominal logic

## References

- Atkey, R. (2009). *Parameterised Notions of Computation*
- Kiselyov, O. & Ishii, H. (2015). *Freer Monads, More Extensible Effects*
- Swierstra, W. (2008). *Data Types à la Carte*
- McBride, C. (2011). *Kleisli Arrows of Outrageous Fortune*
