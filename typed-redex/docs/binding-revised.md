# Binding Support for TypedRedex: Revised Proposals

## The Problem

TypedRedex is a relational/logic programming system. The unbound-generics approach
(functional transformation of concrete terms) doesn't fit well. We need approaches
that work *with* relational semantics.

## Key Insight

In a relational setting, we have two choices for alpha-equivalence:
1. **Bake it into unification** (what I tried, awkward)
2. **Make it an explicit relation** (simpler, more predictable)

---

## Option A: Enhanced De Bruijn (Recommended for Simplicity)

**Idea**: Keep de Bruijn indices but improve ergonomics with:
- Quasiquotation for writing named terms (compile to de Bruijn)
- Pretty-printing that reconstructs names
- Helper relations for shifting/substitution

This is what PLT Redex actually does internally.

### Example

```haskell
-- User writes with a "named" quasi-quoter that compiles to de Bruijn
idTm = [tm| \x. x |]  -- compiles to: Lam (Var Z)

-- Or use a function that does the conversion
idTm = named $ \x -> lam x (var x)

-- Pretty-print reconstructs names
-- show idTm = "λx. x"
```

### Pros
- Simple implementation
- Works perfectly with existing LogicType/unification
- Alpha-equivalence is free (same de Bruijn = same term)
- Proven approach (PLT Redex uses this)

### Cons
- Requires Template Haskell or quasi-quoter for nice syntax
- Internal representation still shows indices

---

## Option B: Named Terms + Explicit Alpha Relation

**Idea**: Use named representation directly. Alpha-equivalence is NOT built into
unification - instead, define it as an explicit relation when needed.

### Types

```haskell
data Tm
  = Var String       -- Just strings, no special Name type
  | Lam String Tm    -- Lambda carries the binder name
  | App Tm Tm
```

### LogicType Instance

```haskell
instance LogicType Tm where
  -- STRUCTURAL unification (not alpha-equiv!)
  unifyVal _ (VarR x) (VarR y) = guard (x == y)
  unifyVal unif (LamR x b) (LamR y b') = guard (x == y) >> unif b b'
  ...
```

### Alpha-Equivalence as Relation

```haskell
-- Define when needed
alphaEq :: (Redex rel) => Judge rel '[Tm, Tm]
alphaEq = judgment "alphaEq" [aeqVar, aeqLam, aeqApp]
  where
    aeqVar = rule "aeq-var" $ fresh $ \x ->
      concl $ alphaEq (var x) (var x)

    aeqLam = rule "aeq-lam" $ fresh5 $ \x y body1 body2 z -> do
      concl $ alphaEq (lam x body1) (lam y body2)
      prem  $ rename x z body1 body1'  -- rename x to fresh z
      prem  $ rename y z body2 body2'  -- rename y to fresh z
      prem  $ alphaEq body1' body2'

    aeqApp = rule "aeq-app" $ fresh4 $ \f1 a1 f2 a2 -> do
      concl $ alphaEq (app f1 a1) (app f2 a2)
      prem  $ alphaEq f1 f2
      prem  $ alphaEq a1 a2
```

### Substitution as Relation

```haskell
-- [e/x]t = r
subst :: (Redex rel) => Judge rel '[String, Tm, Tm, Tm]
subst = judgment "subst" [substVar, substVarNeq, substLam, substApp]
  where
    substVar = rule "subst-var" $ fresh2 $ \x e ->
      concl $ subst x e (var x) e

    substVarNeq = rule "subst-var-neq" $ fresh3 $ \x y e -> do
      concl $ subst x e (var y) (var y)
      prem  $ guard (x /= y)  -- or use a nameNeq relation

    substLam = rule "subst-lam" $ fresh5 $ \x e y body result -> do
      concl $ subst x e (lam y body) (lam y result)
      prem  $ guard (x /= y)           -- Barendregt: x /= bound var
      prem  $ notFreeIn y e            -- Barendregt: y not free in e
      prem  $ subst x e body result

    substApp = rule "subst-app" $ fresh5 $ \x e f a f' a' -> do
      concl $ subst x e (app f a) (app f' a')
      prem  $ subst x e f f'
      prem  $ subst x e a a'
```

### Pros
- Simple LogicType instances (just structural)
- Very explicit - no hidden alpha magic
- User writes exactly what they see
- Works naturally with TypedRedex

### Cons
- Alpha-equivalence not automatic in unification
- Must use `alphaEq` relation explicitly when needed
- Substitution needs freshness/Barendregt side conditions

---

## Option C: Nominal Approach with Freshness Constraints

**Idea**: Add freshness as a first-class constraint to the logic system. This is
the principled approach from nominal logic (Gabbay-Pitts, αProlog).

### Key Concepts

```haskell
-- Freshness constraint: name a is fresh for term t
-- Written: a # t
class HasFreshness rel where
  freshFor :: LTerm Name rel -> LTerm t rel -> rel ()

-- Swapping: swap names a and b in term t
swap :: Name -> Name -> Tm -> Tm
```

### Alpha-Equivalence via Freshness

Two terms `Lam a body1` and `Lam b body2` are alpha-equivalent if:
- There exists a fresh name `c` such that
- `swap a c body1 == swap b c body2`

```haskell
aeqLam = rule "aeq-lam" $ fresh $ \c -> do
  concl $ alphaEq (lam a body1) (lam b body2)
  prem  $ freshFor c body1
  prem  $ freshFor c body2
  prem  $ alphaEq (swap a c body1) (swap b c body2)
```

### Pros
- Principled (based on nominal logic theory)
- Handles complex binding patterns
- Freshness is a constraint, fits relational style

### Cons
- Requires extending TypedRedex with freshness constraints
- More complex implementation
- May be overkill for simple systems

---

## Option D: Contextual / Well-Scoped Indices

**Idea**: Use de Bruijn but with type-level tracking of context depth. This ensures
well-scopedness statically.

```haskell
data Tm (n :: Nat) where
  Var :: Fin n -> Tm n           -- Variable index bounded by context
  Lam :: Tm (S n) -> Tm n        -- Body has one more variable in scope
  App :: Tm n -> Tm n -> Tm n
```

### Pros
- Impossible to create ill-scoped terms
- Very precise types

### Cons
- Complex type-level machinery
- Doesn't play well with LogicType (type indices vary)
- Haskell type system limitations

---

## Recommendation

For TypedRedex, I recommend **Option B (Named + Explicit Alpha)** because:

1. **Fits relational paradigm**: Alpha-equiv as a relation is natural
2. **Simple implementation**: No special LogicType magic
3. **Predictable**: User knows exactly what unification does
4. **Flexible**: Can choose when to use alpha-equiv relation

For convenience, also provide **Option A style** helpers:
- Smart constructors for common patterns
- Pretty-printing with names
- Library of substitution/freshness relations

---

## Comparison Table

| Aspect | A: Enhanced DB | B: Named+Explicit | C: Nominal | D: Well-Scoped |
|--------|----------------|-------------------|------------|----------------|
| User syntax | Quasi-quote | Direct names | Direct names | De Bruijn |
| Alpha in unify | Yes (free) | No (explicit rel) | Via freshness | Yes (free) |
| Implementation | Medium | Simple | Complex | Complex |
| Multi-sorted | Easy | Easy | Easy | Hard |
| TypedRedex fit | Good | Best | Good | Poor |

---

## Proposed API for Option B

```haskell
-- Module: TypedRedex.Binding.Named

-- Simple types (user defines these for their language)
type Name = String

-- Smart constructors (just wrap strings)
name :: String -> LTerm String var
var :: String -> LTerm Tm var
lam :: String -> LTerm Tm var -> LTerm Tm var
app :: LTerm Tm var -> LTerm Tm var -> LTerm Tm var

-- Provided helper relations
nameEq :: (Redex rel) => Judge rel '[String, String]
nameNeq :: (Redex rel) => Judge rel '[String, String]

-- User defines these for their Tm type:
freeVars :: (Redex rel) => Judge rel '[Tm, [String]]
freeIn :: (Redex rel) => Judge rel '[String, Tm]
notFreeIn :: (Redex rel) => Judge rel '[String, Tm]
rename :: (Redex rel) => Judge rel '[String, String, Tm, Tm]
subst :: (Redex rel) => Judge rel '[String, Tm, Tm, Tm]
alphaEq :: (Redex rel) => Judge rel '[Tm, Tm]

-- Typing rules use names directly
typeofLam = rule "typeof-lam" $ fresh4 $ \ctx x tyA body tyB -> do
  concl $ typeof ctx (lam x body) (tarr tyA tyB)
  prem  $ typeof (extend ctx x tyA) body tyB
  -- No unbind needed! x is just a string.
```

---

## What About System F?

With Option B, System F works naturally:

```haskell
data Ty = TUnit | TVar String | TArr Ty Ty | TAll String Ty
data Tm = Unit | Var String | Lam String Ty Tm | App Tm Tm | TLam String Tm | TApp Tm Ty

-- Type-level and term-level names are just strings
-- Use different naming conventions: "x", "y" vs "α", "β"

typeofTLam = rule "typeof-tlam" $ fresh4 $ \ctx a body tyA -> do
  concl $ typeof ctx (tlam a body) (tall a tyA)
  prem  $ typeof ctx body tyA  -- a is free type var in tyA
```

Alpha-equivalence and substitution at both levels are explicit relations.
