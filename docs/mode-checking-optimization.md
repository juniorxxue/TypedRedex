# Optimizing Type-Level Mode Checking in TypedRedex

## Abstract

TypedRedex uses GHC type families to verify at compile-time that relation premises can be scheduled according to their mode annotations (input/output). The original implementation suffered from O(p² · n²) complexity, causing multi-minute compile times and HLS memory exhaustion (10+ GB) for moderately complex rules. We present two optimizations—sorted type-level sets and batch scheduling—that reduce complexity to O(k · p · n), achieving 10-15x speedup in practice.

---

## 1. Problem

### 1.1 Background

TypedRedex is a typed embedding of PLT Redex-style operational semantics in Haskell. Rules are written as:

```haskell
rule "lam" $ do
    (x, tm, env1, env2) <- fresh4 @Nom @Tm @Env @Env
    (ty1, ty2, ty3) <- fresh3 @Ty @Ty @Ty
    prem  $ infer (etrm x ty1 env1) (ctype ty2) tm ty3 env2
    concl $ infer env1 (ctype (tarr ty1 ty2)) (lam (bindT x tm)) (tarr ty1 ty3) env2
```

Each judgment has **mode annotations** declaring which positions are inputs (I) vs outputs (O):

```haskell
infer :: MJudgment5 rel "infer" (In Env) (In Context) (In Tm) (Out Ty) (Out Env)
```

The `CheckSchedule` type family verifies at compile-time that a valid execution order exists: each premise's input variables must be grounded (by conclusion inputs or prior premise outputs) before that premise executes.

### 1.2 The Performance Problem

Users reported:
- **HLS consuming 10+ GB memory** when editing files with complex rules
- **Build times of 3-4 minutes** for a single file with 5 rules
- **Type errors taking minutes to display**

Investigation revealed the bottleneck was type-family evaluation during mode checking.

### 1.3 Complexity Analysis

The original algorithm:

```
CheckSchedule:
  avail := conclusion input variables
  pending := all premises

  while pending ≠ ∅:                    -- O(p) iterations
    for each g in pending:              -- O(p) scan
      if g.inputs ⊆ avail:              -- O(n²) subset check
        execute g
        avail := avail ∪ g.outputs      -- O(n²) union
        remove g from pending
        break
    if no progress: ERROR
```

**Complexity**: O(p) iterations × O(p) scans × O(n²) set operations = **O(p² · n²)**

Where:
- p = number of premises
- n = number of fresh variables

The O(n²) comes from type-level set operations on unsorted lists:

```haskell
-- Original: O(n²) - check membership for each element
type family Subset (xs :: [Nat]) (ys :: [Nat]) :: Bool where
  Subset '[] _ = 'True
  Subset (x ': xs) ys = If (Elem x ys) (Subset xs ys) 'False

-- Elem is O(n)
type family Elem (x :: Nat) (xs :: [Nat]) :: Bool where
  Elem _ '[] = 'False
  Elem x (x ': _) = 'True
  Elem x (_ ': xs) = Elem x xs
```

---

## 2. Solution

### 2.1 Optimization 1: Sorted Type-Level Sets

Replace unsorted lists with **sorted lists** (ascending order by `CmpNat`). This enables O(n) merge-based operations instead of O(n²) search-based operations.

```haskell
-- Insert maintaining sorted order: O(n)
type family Insert (x :: Nat) (xs :: [Nat]) :: [Nat] where
  Insert x '[] = '[x]
  Insert x (y ': ys) = InsertCmp (CmpNat x y) x y ys

type family InsertCmp (o :: Ordering) (x :: Nat) (y :: Nat) (ys :: [Nat]) :: [Nat] where
  InsertCmp 'LT x y ys = x ': y ': ys       -- x < y: insert here
  InsertCmp 'EQ _ y ys = y ': ys            -- x == y: already present
  InsertCmp 'GT x y ys = y ': Insert x ys   -- x > y: keep looking

-- Merge two sorted lists: O(n + m)
type family Union (xs :: [Nat]) (ys :: [Nat]) :: [Nat] where
  Union '[] ys = ys
  Union xs '[] = xs
  Union (x ': xs) (y ': ys) = UnionCmp (CmpNat x y) x xs y ys

type family UnionCmp (o :: Ordering) (x :: Nat) (xs :: [Nat])
                     (y :: Nat) (ys :: [Nat]) :: [Nat] where
  UnionCmp 'LT x xs y ys = x ': Union xs (y ': ys)
  UnionCmp 'EQ x xs _ ys = x ': Union xs ys
  UnionCmp 'GT x xs y ys = y ': Union (x ': xs) ys

-- Subset check on sorted lists: O(n + m)
type family Subset (xs :: [Nat]) (ys :: [Nat]) :: Bool where
  Subset '[] _ = 'True
  Subset (_ ': _) '[] = 'False
  Subset (x ': xs) (y ': ys) = SubsetCmp (CmpNat x y) x xs y ys

type family SubsetCmp (o :: Ordering) (x :: Nat) (xs :: [Nat])
                      (y :: Nat) (ys :: [Nat]) :: Bool where
  SubsetCmp 'LT _ _ _ _ = 'False              -- x < y: x not in ys
  SubsetCmp 'EQ _ xs _ ys = Subset xs ys      -- found, continue
  SubsetCmp 'GT x xs _ ys = Subset (x ': xs) ys  -- skip y
```

### 2.2 Optimization 2: Batch Scheduling

Replace one-at-a-time premise selection with **batch partitioning**: in each iteration, process *all* ready premises simultaneously.

```haskell
-- Partition into (ready, notReady) in single pass: O(p · n)
type family Partition (avail :: [Nat]) (gs :: [Goal]) :: ([Goal], [Goal]) where
  Partition _ '[] = '( '[], '[] )
  Partition avail (g ': gs) = PartitionStep (IsReady avail g) g (Partition avail gs)

type family PartitionStep (ready :: Bool) (g :: Goal)
                          (rest :: ([Goal], [Goal])) :: ([Goal], [Goal]) where
  PartitionStep 'True  g '( ready, notReady ) = '( g ': ready, notReady )
  PartitionStep 'False g '( ready, notReady ) = '( ready, g ': notReady )

-- Batch solve: process all ready premises at once
type family Solve (avail :: [Nat]) (pending :: [Goal]) :: SolveResult where
  Solve _ '[] = 'Solved
  Solve avail pending = SolveStep (Partition avail pending) avail

type family SolveStep (partition :: ([Goal], [Goal])) (avail :: [Nat]) :: SolveResult where
  SolveStep '( '[], notReady ) avail = 'Stuck avail notReady
  SolveStep '( ready, notReady ) avail =
    Solve (Union avail (CollectOutputs ready)) notReady
```

This reduces iterations from p (one premise per iteration) to k (number of dependency stages).

### 2.3 Combined Complexity

| Component | Original | Optimized |
|-----------|----------|-----------|
| Subset check | O(n²) | O(n) |
| Union | O(n²) | O(n) |
| Iterations | O(p) | O(k) |
| Per-iteration scan | O(p) | O(p) |
| **Total** | **O(p² · n²)** | **O(k · p · n)** |

Where k ≤ p is the number of dependency stages (typically 1-3 for most rules).

---

## 3. Results

### 3.1 Build Time Comparison

Test environment: Apple M1, GHC 9.10.1, macOS

| Test Case | Before | After | Speedup |
|-----------|--------|-------|---------|
| example-poly (5 rules, ~10 vars each) | ~3-4 min | ~19 sec | **10-15x** |
| Clean build with complex TestTypeCheck | >5 min | ~25 sec | **>12x** |

### 3.2 HLS Behavior

- **Before**: 10+ GB memory usage, unresponsive, frequent crashes
- **After**: Normal memory usage (~500 MB), responsive type checking

### 3.3 Theoretical Scaling

For a rule with p premises and n fresh variables:

| Scenario | k | p | n | Original O(p²n²) | Optimized O(kpn) | Ratio |
|----------|---|---|---|------------------|------------------|-------|
| Simple | 1 | 2 | 4 | 64 | 8 | 8x |
| Medium | 2 | 4 | 8 | 1,024 | 64 | 16x |
| Complex | 3 | 6 | 12 | 5,184 | 216 | 24x |
| Large | 4 | 8 | 16 | 16,384 | 512 | 32x |

The speedup grows with rule complexity, exactly where it's needed most.

---

## 4. Conclusion

Type-level computation in GHC can be a powerful tool for compile-time verification, but naive algorithms can lead to severe performance problems. By applying standard algorithmic techniques—sorted data structures and batch processing—we achieved order-of-magnitude improvements in compile-time performance.

Key lessons:
1. **Type families are Turing-complete** but lack memoization—complexity matters
2. **CmpNat enables efficient type-level sorting** via merge-based algorithms
3. **Batch processing reduces iteration count** from worst-case to structural depth

The optimized mode checker now scales to real-world type system implementations without impacting developer experience.
