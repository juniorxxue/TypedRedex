# TypedRedex-HKT: Q&A

## Q: What's `Var` and `Con`? Where does it come from, and motivation?

`Var` and `Con` are the two constructors of `Term f` (in HKT/Core.hs):

```haskell
data Term (f :: Type -> Type) where
  Var_ :: VarId -> Term f           -- A logic variable
  Con_ :: f (Term f) -> Term f      -- A constructor with children

pattern Var :: VarId -> Term f
pattern Con :: f (Term f) -> Term f
```

### Motivation

**The core insight**: In logic programming, a term is either:
1. A **variable** (unbound, to be unified later)
2. A **constructor** (ground structure with children that may contain variables)

This is exactly miniKanren's representation.

### How It Works with Functors

Given a base functor:
```haskell
data TyF r = TUnit | TArr r r
```

`Term TyF` gives you:
```haskell
-- A variable (unknown type)
Var (VarId 0) :: Term TyF

-- Ground unit type
Con TUnit :: Term TyF

-- Arrow with children that can be variables
Con (TArr (Var (VarId 0)) (Var (VarId 1))) :: Term TyF
--         ^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^
--         children are Term TyF, not TyF!
```

### Comparison with Current Approach

Current TypedRedex embeds variables directly in each sort:
```haskell
data Ty = TyVar VarId | TInt | TArr Ty Ty
data Expr = ExprVar VarId | ELam Expr | ...
```

HKT factors out the "variable or constructor" pattern:
```haskell
data TyF r = TInt | TArr r r          -- No TyVar here!
type Ty = Term TyF                     -- Variables come from Term
```

### Why Pattern Synonyms?

The actual constructors are `Var_` and `Con_` (with underscores). Pattern synonyms `Var`/`Con` provide a cleaner API and allow future internal changes without breaking user code.

The `{-# COMPLETE Var, Con #-}` pragma tells GHC these patterns are exhaustive, avoiding incomplete-pattern warnings.

---

## Q: Brainstorm more, and conclude pros and cons of switching to HKT, in terms of writing interpreters, examples, and others.

### Architecture Overview

**Current Approach** (3 packages, ~4400 lines):
```
typedredex-logic (489 lines)   - LogicType, Redex typeclass hierarchy
typedredex-dsl (2371 lines)    - Moded DSL, TH derivation
typedredex-interp (1540 lines) - SubstRedex interpreter, tracing, typesetting
```

**HKT Approach** (1 package, ~600 lines demo):
```
typedredex-hkt/HKT.Core   (~100 lines) - Term f, Fix f, VarId
typedredex-hkt/HKT.Moded  (~480 lines) - Type-level mode checking
```

---

### 1. Type Representation

**Current**: Each type has TWO representations
```haskell
-- The "normal" type
data Ty = TInt | TArr Ty Ty

-- The "logic" type (via LogicType)
instance LogicType Ty where
  data Reified Ty var = TIntR | TArrR (Logic Ty var) (Logic Ty var)
  --                                  ^^^^^^^^^^^^^ children wrapped in Logic
```

**HKT**: ONE functor, TWO wrappers
```haskell
data TyF r = TInt | TArr r r   -- Single definition

type Ty   = Fix TyF            -- Plain recursive
type TyTm = Term TyF           -- Logic term (Var | Con)
```

**Impact on Interpreters**:
- Current: Interpreter must handle `Logic a var` wrapper at each child
- HKT: Interpreter handles `Term f` uniformly - `Var` or `Con` at any level

---

### 2. Interpreter Implementation

**Current SubstRedex** (`Subst.hs`, 196 lines):
```haskell
data Subst s = Subst
  { subst :: forall t. V s t -> Maybe t  -- Type-indexed substitution!
  , nextVar :: VarRepr
  , ...
  }

-- Unification dispatches to LogicType's unifyVal
unify :: Logic a -> Logic a -> Goal rel
-- Each type's unifyVal does structural matching
```

**HKT Interpreter** (would be ~100 lines):
```haskell
data Subst = Subst
  { subst :: IntMap SomeTerm  -- Single map, not type-indexed
  , nextVar :: Int
  }

-- Generic unification via Traversable
unify :: (Eq1 f, Traversable f) => Term f -> Term f -> StateT Subst Maybe ()
unify (Var x) t = bind x t
unify (Con f1) (Con f2)
  | eq1 f1 f2 = zipWithM_ unify (toList f1) (toList f2)  -- Generic!
  | otherwise = empty
```

**Key Difference**:
- Current: Type-indexed substitution (`V s t -> Maybe t`), each type implements `unifyVal`
- HKT: Single untyped map, generic unification via `Traversable`

---

### 3. Adding a New Sort

**Current** (manual):
```haskell
-- 1. Define type
data Kind = KType | KArr Kind Kind

-- 2. Define LogicType instance (~20 lines)
instance LogicType Kind where
  data Reified Kind var = KTypeR | KArrR (Logic Kind var) (Logic Kind var)
  project KType = KTypeR
  project (KArr k1 k2) = KArrR (Ground $ project k1) (Ground $ project k2)
  reify KTypeR = Just KType
  reify (KArrR k1 k2) = KArr <$> reifyLogic k1 <*> reifyLogic k2
  unifyVal _ KTypeR KTypeR = pure ()
  unifyVal u (KArrR a b) (KArrR c d) = u a c >> u b d
  unifyVal _ _ _ = empty
  children KTypeR = []
  children (KArrR a b) = [Field (Proxy @Kind) a, Field (Proxy @Kind) b]
  quote KTypeR = quote0 "KType"
  quote (KArrR a b) = quote2 "KArr" a b
```

**Current** (with TH):
```haskell
data Kind = KType | KArr Kind Kind
deriveLogicType ''Kind ['KType ~> "KType", 'KArr ~> "KArr"]
```

**HKT**:
```haskell
data KindF r = KType | KArr r r
  deriving (Eq, Show, Functor, Foldable, Traversable)

-- Smart constructors (2 lines)
ktype = con0 KType
karr = con2 KArr
```

**Comparison**:
| Aspect | Current (manual) | Current (TH) | HKT |
|--------|------------------|--------------|-----|
| Lines per sort | ~20 | ~2 | ~4 |
| Unification | Per-type | Per-type (generated) | Generic |
| TH dependency | No | Yes | No |

---

### 4. Mode System

**Current** (`Moded.hs`, 1030 lines): Runtime scheduling
```haskell
-- Premises reordered at RUNTIME based on groundedness
prem $ synth ctx e1 (tarr a b)  -- Executes when ctx, e1 are ground
prem $ check ctx e2 a           -- Executes when ctx, e2, a are ground
```

**HKT** (`Moded.hs`, 480 lines): Compile-time verification
```haskell
-- Type-level tracking of variable IDs
-- Compile ERROR if no valid schedule exists
ruleM @"⇒App" $ do
  (ctx, e1, e2, a, b) <- fresh5
  concl $ synth ctx (eapp e1 e2) b
  prem  $ synth ctx e1 (tarr a b)  -- Type says: needs [ctx,e1], produces [a,b]
  prem  $ check ctx e2 a           -- Type says: needs [ctx,e2,a], produces []
```

**Trade-off**:
- Current: More flexible (runtime adaptation), larger code
- HKT: Catches errors earlier (compile-time), but less flexible

---

### 5. Interpreter Extensibility (Redex Hierarchy)

**Current**: Rich typeclass hierarchy
```haskell
class Redex rel where ...           -- Core: fresh, unify
class Redex rel => RedexEval rel    -- Evaluation: derefVar
class Redex rel => RedexNeg rel     -- Negation: neg
class Redex rel => RedexFresh rel   -- Fresh atoms: freshInt
class Redex rel => RedexHash rel    -- Freshness: hash
class Redex rel => RedexStructure rel  -- Tracing: onRuleEnter/Exit
```

**HKT** (as demoed): Simpler, but less extensible
- No tracing hooks
- No negation
- No nominal logic support

**To match current features**, HKT would need similar hierarchy - the functor approach doesn't inherently simplify this.

---

### 6. Presentation Layer (Tracing, Typesetting)

**Current**:
- `Tracing.hs` (504 lines) - Derivation trees via `RedexStructure`
- `Typesetting.hs` (409 lines) - LaTeX generation
- `quote` method in `LogicType` for pretty-printing

**HKT**:
- Would need similar infrastructure
- `quote` equivalent: could use `Show1` or custom class
- Tracing: would need hooks in the monad

**No significant difference** - presentation concerns are orthogonal to term representation.

---

### 7. Summary: Pros and Cons

#### HKT Pros
1. **Simpler AST definition** - One functor, derive `Traversable`
2. **Generic unification** - No per-type implementation
3. **Compile-time mode checking** - Catches scheduling errors early
4. **No TH required** - For basic functionality
5. **Cleaner conceptual model** - `Term f = Var | Con (f (Term f))`

#### HKT Cons
1. **Pattern matching overhead** - Always handle `Var`/`Con`
2. **Lost type information in substitution** - Single `IntMap` vs type-indexed
3. **Nominal logic harder** - Current's `NominalAtom` + `Hash` machinery doesn't translate directly
4. **No derivation tracing** (in demo) - Would need to add
5. **Complex type errors** - Type-level mode checking can produce cryptic messages
6. **Less mature** - Current approach is battle-tested

#### Current Approach Pros
1. **Rich feature set** - Negation, nominal atoms, tracing, typesetting
2. **Type-indexed substitution** - More type safety in interpreter
3. **TH handles boilerplate** - `deriveLogicType` is mature
4. **Runtime mode flexibility** - Adapts to actual groundedness
5. **Better error messages** - Simpler types

#### Current Approach Cons
1. **Dual representation** - `Ty` vs `Reified Ty var`
2. **Per-type unification** - Even with TH, it's generated per type
3. **Large codebase** - 4400 lines of infrastructure
4. **TH dependency** - For practical use

---

### Recommendation

**For the paper/research**: HKT is interesting because:
- Novel type-level mode checking
- Cleaner theoretical foundation (functors + Traversable)
- Good "novelty story" for publication

**For practical use**: Current approach is more complete:
- Nominal logic, negation, tracing all work
- TH eliminates most boilerplate
- Proven on real examples

**Possible path forward**:
- Use HKT ideas to simplify `LogicType` (make `Reified` a functor)
- Keep current interpreter infrastructure
- Add compile-time mode checking as optional layer

---

## Q: Explain more about "Pattern matching overhead - Always handle Var/Con", and compare with existing approach

### Structure Comparison

**Current Approach**:
```haskell
-- Two-level: Logic wraps Reified
data Logic a var = Free (Var a var)        -- Variable
                 | Ground (Reified a var)  -- Constructor

-- Reified is per-type, ONLY constructors (no variable case)
data Reified Ty var = TUnitR
                    | TArrR (Logic Ty var) (Logic Ty var)
```

**HKT Approach**:
```haskell
-- Two-level: Term wraps functor
data Term f = Var VarId              -- Variable
            | Con (f (Term f))       -- Constructor

-- Functor is per-type, ONLY constructors (no variable case)
data TyF r = TUnit
           | TArr r r
```

They're structurally isomorphic! Both have the same layering.

---

### Where the Difference Matters: Interpreter Code

**Current `unifyVal`** - only handles constructors:
```haskell
-- In LogicType instance for Ty
unifyVal :: Unifier rel var -> Reified Ty var -> Reified Ty var -> rel ()
unifyVal _ TUnitR TUnitR = pure ()
unifyVal u (TArrR a1 a2) (TArrR b1 b2) = u a1 b1 >> u a2 b2
unifyVal _ _ _ = empty  -- Different constructors fail

-- Variables handled SEPARATELY in Logic layer (Subst.hs):
unify :: Logic a -> Logic a -> Goal rel
unify (Free v1) (Free v2) = ...   -- var-var
unify (Free v) (Ground r) = ...   -- var-ground
unify (Ground r) (Free v) = ...   -- ground-var
unify (Ground r1) (Ground r2) = unifyVal unify r1 r2  -- delegates to unifyVal
```

**HKT `unify`** - handles everything in one place:
```haskell
unify :: (Eq1 f, Traversable f) => Term f -> Term f -> StateT Subst Maybe ()
unify (Var x) t = bind x t
unify t (Var x) = bind x t
unify (Con f1) (Con f2)
  | eq1Shape f1 f2 = zipWithM_ unify (toList f1) (toList f2)
  | otherwise = empty
```

**The "overhead" I mentioned**: In HKT, every function that inspects terms must handle `Var`/`Con`. In current approach, `unifyVal` only sees `Reified` (constructors).

---

### For Users Writing Rules: NO DIFFERENCE

Users never pattern match directly. Both use smart constructors:

**Current**:
```haskell
ruleM @"⇐λ" $ do
  (ctx, body, a, b) <- fresh4
  concl $ check ctx (elam body) (tarr a b)   -- smart constructors
```

**HKT**:
```haskell
ruleM @"⇐λ" $ do
  (ctx, body, a, b) <- fresh4
  concl $ check ctx (elam body) (tarr a b)   -- identical!
```

---

### Where Pattern Matching Matters: Custom Logic

If you need custom matching (e.g., in `succ_` helper in Rules.hs):

**Current** (would need):
```haskell
succ_ :: LTerm Nat rel -> LTerm Nat rel
succ_ (Ground (SR n)) = Ground (SR (Ground (SR n)))  -- wrap in S
succ_ t = t  -- variable stays as-is
```

**HKT**:
```haskell
succ_ :: T vs ExprF -> T vs ExprF
succ_ (T v (Con (EVar i))) = T v (Con (EVar (i + 1)))
succ_ t = t
```

Both require knowing the structure. The HKT version is arguably cleaner because `Con` is uniform across all types.

---

### Real Overhead: Writing Traversals

**Current**: Each type implements `children`, `derefVal`, etc.
```haskell
children :: Reified Ty var -> [Field Ty var]
children TUnitR = []
children (TArrR a b) = [Field (Proxy @Ty) a, Field (Proxy @Ty) b]

derefVal :: Evaluator rel var -> Reified Ty var -> rel Ty
derefVal _ TUnitR = pure TUnit
derefVal e (TArrR a b) = TArr <$> e a <*> e b
```

**HKT**: Generic via `Traversable` - no per-type code needed!
```haskell
-- Automatic from: deriving (Functor, Foldable, Traversable)
-- No children/derefVal implementation needed
```

---

### Summary

| Aspect | Current | HKT |
|--------|---------|-----|
| User rule syntax | Same | Same |
| Interpreter unification | Per-type `unifyVal` | Generic via `Traversable` |
| Custom pattern matching | `Ground (TArrR ...)` | `Con (TArr ...)` |
| Traversals (children, deref) | Manual per-type | Derived automatically |
| Variable handling | Separated (Logic layer) | Inline (every function) |

**Conclusion**: The "overhead" is not about syntax verbosity. It's about:
1. HKT requires `Var`/`Con` handling in every term-inspecting function
2. But HKT eliminates per-type traversal boilerplate via `Traversable`

The trade-off favors HKT when you have many types, and favors current approach when you have complex custom logic that benefits from the separated variable handling.
