# TypedRedex API Improvement Proposals

## Executive Summary

This document analyzes the TypedRedex library's current API design and proposes improvements to reduce verbosity, particularly around the `Applied*` type family pattern. The current design prioritizes clean rule bodies at the cost of verbose type signatures.

---

## Current Pain Points

### 1. Verbose Applied Type Signatures

```haskell
-- Current: Must write all type parameters explicitly
substTyVar :: (Redex rel)
           => LTerm Nat rel -> LTerm Ty rel -> LTerm Nat rel -> LTerm Ty rel
           -> Applied4 rel Nat Ty Nat Ty
```

The type signature has significant redundancy:
- `Applied4` duplicates the arity information
- `Nat Ty Nat Ty` duplicates argument types already visible in the function parameters
- `rel` appears 5 times

### 2. Arity-Indexed Type Families

The library provides separate types and functions for each arity:
- Types: `Applied`, `Applied2`, `Applied3`, `Applied4`, `Applied5`
- Rules: `rule`, `rule2`, `rule3`, `rule4`, `rule5`
- Judgments: `judgment`, `judgment2`, `judgment3`, `judgment4`, `judgment5`
- Fresh: `fresh`, `fresh2`, `fresh3`, `fresh4`, `fresh5`

This requires users to manually track arities and select the right combinators.

### 3. LogicType Boilerplate

Each data type requires a substantial `LogicType` instance:
```haskell
instance LogicType Ty where
  data Reified Ty var = TUnitR | TArrR (Logic Ty var) (Logic Ty var)
  project TUnit = TUnitR
  project (TArr a b) = TArrR (Ground $ project a) (Ground $ project b)
  reify TUnitR = Just TUnit
  reify (TArrR (Ground a) (Ground b)) = TArr <$> reify a <*> reify b
  reify _ = Nothing
  quote TUnitR = quote0 "Unit" TUnitR
  quote (TArrR a b) = quote2 "TArrR" TArrR a b
  unifyVal _ TUnitR TUnitR = pure ()
  unifyVal unif (TArrR a b) (TArrR a' b') = unif a a' *> unif b b'
  unifyVal _ _ _ = empty
  derefVal _ TUnitR = pure TUnit
  derefVal deref (TArrR a b) = TArr <$> deref a <*> deref b
```

---

## Proposal 1: Type-Level HList for Unified Arity

**Goal**: Replace `Applied`, `Applied2`, ..., `Applied5` with a single polymorphic type.

### Design

Use type-level lists (DataKinds) to encode argument types:

```haskell
{-# LANGUAGE DataKinds, TypeFamilies, TypeOperators, GADTs #-}

-- Type-level list for argument types
type Applied rel (ts :: [Type]) = AppliedN rel ts

data AppliedN rel (ts :: [Type]) where
  Applied0 :: rel () -> AppliedN rel '[]
  AppliedS :: LTerm t rel -> AppliedN rel ts -> AppliedN rel (t ': ts)

-- Type family to extract goal
type family GoalOf (app :: Type) :: Type where
  GoalOf (AppliedN rel ts) = rel ()

-- Smart constructor (via type class)
class MkApplied ts rel where
  mkApplied :: HList (Map (Flip LTerm rel) ts) -> rel () -> AppliedN rel ts

-- Example relation now becomes:
substTyVar :: (Redex rel) => Relation rel '[Nat, Ty, Nat, Ty]
-- or with type alias:
type SubstRel rel = Relation rel '[Nat, Ty, Nat, Ty]
```

### Benefits

1. **Single type for all arities**: No more `Applied4` vs `Applied3` confusion
2. **Arity-polymorphic functions**: One `judgment` function for all arities
3. **Self-documenting**: `'[Nat, Ty, Nat, Ty]` clearly shows argument types

### Trade-offs

- Requires more advanced type-level programming (DataKinds, TypeFamilies)
- May produce more complex error messages
- Compilation time may increase slightly

### Implementation Sketch

```haskell
-- Single judgment combinator
judgment :: forall ts rel. (AllLogicType ts, Redex rel)
         => String -> [Rule rel ts] -> Judgment rel ts

-- Variadic fresh using type-level lists
freshN :: forall ts rel. AllLogicType ts => (HList (LTerms ts rel) -> rel ()) -> rel ()

-- Example usage would become:
substTyVar :: Redex rel => Judgment rel '[Nat, Ty, Nat, Ty]
substTyVar = judgment "substTyVar" [substVarEq, substVarLt, substVarGt]
```

---

## Proposal 2: Inferred Return Types via Functional Dependencies

**Goal**: Eliminate explicit `Applied*` return types through type inference.

### Design

Use functional dependencies to let GHC infer the Applied type from the function arguments:

```haskell
class JudgmentResult args result | args -> result where
  type ResultApplied args rel :: Type

-- Instances for different arities (auto-selected)
instance JudgmentResult (a -> b -> Applied2 rel a b) (Applied2 rel a b)
instance JudgmentResult (a -> b -> c -> Applied3 rel a b c) (Applied3 rel a b c)
-- etc.

-- New judgment signature (no explicit Applied in signature)
judgment :: (Redex rel, JudgmentResult f result, result ~ Applied_ rel)
         => String -> [Rule_ rel] -> f
```

### Alternative: Type Synonym with Visible Forall

```haskell
-- User defines a type synonym once
type Subst4 rel a b c d = Applied4 rel a b c d

-- Then use it consistently
substTy :: Redex rel => Subst4 rel Nat Ty Ty Ty
-- or even shorter with partial application:
type SubstTy rel = Applied4 rel Nat Ty Ty Ty
```

### Benefits

1. **No changes to core architecture**
2. **Gradual adoption**: Users can use type synonyms immediately
3. **Better error messages**: Type synonyms show semantic intent

### Trade-offs

- Type synonyms are just aliases, not real abstraction
- Still requires tracking arity manually
- Functional dependencies approach is complex to implement correctly

---

## Proposal 3: Template Haskell Derivation for LogicType

**Goal**: Automatically derive `LogicType` instances to reduce boilerplate.

### Design

Provide a TH function that generates all boilerplate:

```haskell
-- User writes:
data Ty = TUnit | TArr Ty Ty
deriveLogicType ''Ty

-- TH generates the full LogicType instance automatically
```

### Implementation Sketch

```haskell
deriveLogicType :: Name -> Q [Dec]
deriveLogicType name = do
  info <- reify name
  case info of
    TyConI (DataD _ _ _ _ cons _) -> do
      -- Generate Reified data family instance
      reifiedDec <- mkReifiedInstance name cons
      -- Generate project/reify/quote/unifyVal/derefVal
      methodDecs <- mapM (mkMethod name cons)
        [''project, ''reify, ''quote, ''unifyVal, ''derefVal]
      pure (reifiedDec : methodDecs)
```

### Advanced: Derive with Custom Names

```haskell
deriveLogicTypeWith ''Ty
  [ ('TUnit, "Unit")   -- custom quote name
  , ('TArr, "->")      -- use arrow for display
  ]
```

### Benefits

1. **Dramatic boilerplate reduction**: 20+ lines per type -> 1 line
2. **Consistency**: Generated code follows best practices
3. **Maintainability**: Adding constructors requires no manual changes

### Trade-offs

- TH increases compile times
- TH-generated code can be harder to debug
- Not all users are comfortable with TH

---

## Proposal 4: Record-Style Relations with Named Fields

**Goal**: Replace positional arguments with named fields for clarity.

### Design

Instead of position-based arguments, use records:

```haskell
-- Current (positional, error-prone):
substTy depth subTy ty result

-- Proposed (named, self-documenting):
data SubstTyArgs = SubstTyArgs
  { substDepth  :: LTerm Nat rel
  , substWith   :: LTerm Ty rel
  , substIn     :: LTerm Ty rel
  , substResult :: LTerm Ty rel
  }

substTy :: Redex rel => SubstTyArgs rel -> Applied rel SubstTyArgs
```

### With Overloaded Labels (GHC 9.2+)

```haskell
-- Using OverloadedRecordDot and OverloadedLabels
substVar = rule "subst-var" $ freshArgs @SubstTyArgs $ \args -> do
  concl $ substTy args
  prem  $ natEq args.depth args.varIndex
```

### Benefits

1. **Self-documenting**: Field names explain semantics
2. **Refactoring-safe**: Reordering arguments doesn't break code
3. **IDE support**: Better autocomplete with record fields

### Trade-offs

- More verbose for simple relations
- Requires defining record types for each relation
- May not match mathematical notation style

---

## Proposal 5: Operator-Based DSL Improvements

**Goal**: Reduce syntactic noise in rule definitions.

### Subproposal 5a: Unicode Operators

```haskell
-- Current:
concl $ typeof ctx e ty
prem  $ lookup' ctx n ty

-- With unicode (optional import):
∴ typeof ctx e ty  -- conclusion (therefore)
∵ lookup' ctx n ty  -- premise (because)
```

### Subproposal 5b: Implicit Fresh with Patterns

Use view patterns or pattern synonyms:

```haskell
-- Current:
rule3 "lookup-here" $ fresh2 $ \ty rest ->
  concl $ lookup' (cons ty rest) zro ty

-- Proposed: pattern-based syntax
rule3 "lookup-here" $
  concluding $ \(cons ?ty ?rest, zro, ?ty) ->
    -- ?ty and ?rest are automatically fresh
    pure ()
```

### Subproposal 5c: Do-Notation Sugar

```haskell
-- Current:
rule3 "typeof-app" $ fresh5 $ \ctx e1 e2 tyA tyB -> do
  concl $ typeof ctx (app e1 e2) tyB
  prem  $ typeof ctx e1 (tarr tyA tyB)
  prem  $ typeof ctx e2 tyA

-- Proposed: RebindableSyntax or QualifiedDo
rule3 "typeof-app" $ Judgment.do
  (ctx, app e1 e2, tyB) <- conclusion
  typeof ctx e1 (tarr tyA tyB)
  typeof ctx e2 tyA
```

### Benefits

1. **More concise rule bodies**
2. **Closer to mathematical notation**
3. **Reduced cognitive load**

### Trade-offs

- Unicode may not work in all editors/terminals
- Custom do-notation can confuse newcomers
- Pattern-based approach requires sophisticated type-level programming

---

## Recommendation Priority

Based on impact vs. implementation complexity:

| Priority | Proposal | Impact | Complexity | Recommendation |
|----------|----------|--------|------------|----------------|
| 1 | **TH Derivation** | High | Medium | Implement first - biggest productivity win |
| 2 | **Type-Level HList** | High | High | Long-term goal - unifies the API |
| 3 | **Type Synonyms** | Medium | Low | Document as best practice now |
| 4 | **Record-Style** | Medium | Medium | Consider for new relations |
| 5 | **Operator DSL** | Low | Low | Nice-to-have, add gradually |

## Immediate Actionable Items

1. **Document type synonym convention** in library documentation:
   ```haskell
   -- Recommended: Define type aliases for your relations
   type Lookup rel = Applied3 rel Ctx Nat Ty
   type SubstTy rel = Applied4 rel Nat Ty Ty Ty
   ```

2. **Add TH module** `TypedRedex.TH.Derive` for automatic LogicType derivation

3. **Prototype HList approach** in a separate branch to evaluate type error quality

---

## Appendix: Comparison with PLT Redex

| Feature | PLT Redex | TypedRedex Current | TypedRedex Proposed |
|---------|-----------|-------------------|---------------------|
| Relation arity | Untyped | Explicit (Applied4) | Inferred (HList) |
| Type checking | Runtime | Compile-time | Compile-time |
| Boilerplate | Low | High | Medium (with TH) |
| Error messages | Good | Variable | Improved |

The proposals aim to bring TypedRedex closer to PLT Redex's ergonomics while maintaining its type safety advantages.
