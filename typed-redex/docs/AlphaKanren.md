# AlphaKanren: Nominal Logic for TypedRedex

> Proposal for supporting lambda binding with named variables instead of de Bruijn indices.

---

## AlphaKanren vs Locally-Nameless (unbound)

There are two main approaches to handling binders without raw de Bruijn indices:

| Aspect | Locally-Nameless (unbound) | Nominal (alphaKanren) |
|--------|---------------------------|----------------------|
| **Representation** | Bound vars = indices, free vars = names | All vars = names (atoms) |
| **Opening binder** | Substitute index 0 with fresh name | Just return the name already there |
| **Alpha-equivalence** | Structural after opening | Built into unification |
| **Freshness** | Implicit via `FreshM` monad | Explicit constraints (`a # t`) or implicit |
| **Substitution** | Shift indices when going under binders | Swap names (permutations) |

### Locally-Nameless (unbound style)

```
λ. 0          -- body uses index 0 for bound var
              -- "opening" replaces 0 with fresh name x
λ. x          -- after opening
```

- **Pros**: No need to track freshness explicitly; indices guarantee no capture
- **Cons**: Still need shifting logic internally; two representations (bound vs free)

### Nominal Logic (alphaKanren style)

```
λx. x         -- body directly uses name x
              -- "opening" just returns x (already there!)
```

- **Pros**: Single representation; unification handles alpha-equivalence
- **Cons**: Need freshness constraints to avoid capture during substitution

### Our Choice: Nominal with Implicit Freshness

We use **nominal style** (names everywhere) but hide freshness constraints inside `unbind`:

```haskell
-- User writes:
(x, body) <- unbind bnd

-- Library internally ensures x is fresh w.r.t. current scope
-- No explicit "hash" constraints needed
```

This gives the **simplicity of nominal** (no indices) with the **ergonomics of unbound** (implicit freshness).

---

## Motivation

Currently, TypedRedex examples use de Bruijn indices (`Var Nat`) for variable binding, forcing users to reason about shifting and index arithmetic. This proposal adds **nominal logic programming** support inspired by [alphaKanren](https://github.com/webyrd/alphaKanren) and the [unbound](https://hackage.haskell.org/package/unbound) library, so users can write:

```haskell
-- Instead of:   Lam (Var Z)
-- Write:        lam (bind x (var x))

typeofLam = rule "T-Lam" $ do
  [ctx, tyA, tyB, bnd] <- freshVars
  concl $ typeof ctx (lam tyA bnd) (tarr tyA tyB)
  (x, body) <- unbind bnd   -- Fresh name, implicit freshness!
  prem $ typeof (extend x tyA ctx) body tyB
```

**Key benefits:**
- No de Bruijn indices or shifting
- Alpha-equivalence handled automatically by unification
- Capture-avoiding substitution built-in via `instantiate`
- Clean, readable rules that match paper notation

---

## Core API

### Nominal Atoms

Ground names (distinct from logic variables) representing bound variable names:

```haskell
-- Abstract types (don't expose constructors)
data Nom      -- Term variable names
data TyNom    -- Type variable names (System F)

-- Create fresh atoms in relations
freshNom   :: Redex rel => rel (LTerm Nom rel)
freshTyNom :: Redex rel => rel (LTerm TyNom rel)
```

### Binders

Opaque binder type with **alpha-equivalence built into unification**:

```haskell
-- Bind a name in a body (abstract type)
data Bind name body

-- For type-level binders (System F)
data TyBind name body
```

**Key property**: `bind x (var x) == bind y (var y)` under unification.

### Creating Binders

```haskell
-- Create a binder
bind   :: LTerm Nom rel   -> LTerm body rel -> LTerm (Bind Nom body) rel
bindTy :: LTerm TyNom rel -> LTerm body rel -> LTerm (TyBind TyNom body) rel
```

### Opening Binders (`unbind`)

Open a binder with a **fresh** name. Freshness constraints are implicit:

```haskell
-- Returns (fresh_name, body_with_name)
unbind   :: Redex rel => LTerm (Bind Nom body) rel   -> rel (LTerm Nom rel, LTerm body rel)
unbindTy :: Redex rel => LTerm (TyBind TyNom body) rel -> rel (LTerm TyNom rel, LTerm body rel)
```

### Instantiation (β-reduction)

Substitute a term/type for the bound variable. Requires a `Subst` instance (see below):

```haskell
-- For β-reduction: (λx.e) v  →  [v/x]e
instantiate   :: (Redex rel, Subst Nom body)
              => LTerm (Bind Nom body) rel
              -> LTerm body rel
              -> rel (LTerm body rel)

-- For type application: (Λα.e) [A]  →  [A/α]e
instantiateTy :: (Redex rel, Subst TyNom body)
              => LTerm (TyBind TyNom body) rel
              -> LTerm body rel
              -> rel (LTerm body rel)
```

---

## What Users Must Provide

The library provides `Nom`, `Bind`, `unbind`, and generic `instantiate`. However, `instantiate` needs to traverse user-defined syntax, so users must provide a **`Subst` instance**.

### The `Subst` Typeclass

```haskell
-- Provided by library
class Subst name term where
  -- | Substitute: [arg/x]term
  subst :: name -> term -> term -> term
```

### User Implements for Their Syntax

For STLC terms:

```haskell
instance Subst Nom Tm where
  subst x arg = go
    where
      go (Var y)
        | x == y    = arg      -- Replace bound variable
        | otherwise = Var y    -- Different variable, keep as-is
      go (Lam ty bnd) = Lam ty (substBind x arg bnd)  -- Library helper
      go (App e1 e2)  = App (go e1) (go e2)
      go Unit         = Unit
```

For System F, also need substitution in types:

```haskell
instance Subst TyNom Ty where
  subst alpha arg = go
    where
      go (TVar beta)
        | alpha == beta = arg
        | otherwise     = TVar beta
      go (TArr a b)     = TArr (go a) (go b)
      go (TForall bnd)  = TForall (substBind alpha arg bnd)

-- Type substitution in terms (for type application)
instance Subst TyNom Tm where
  subst alpha arg = go
    where
      go (Var x)        = Var x  -- Term var, unchanged
      go (Lam ty bnd)   = Lam (subst alpha arg ty) (substBind alpha arg bnd)
      go (App e1 e2)    = App (go e1) (go e2)
      go (TyLam bnd)    = TyLam (substBind alpha arg bnd)
      go (TyApp e ty)   = TyApp (go e) (subst alpha arg ty)
```

### Library-Provided Helpers

```haskell
-- Substitute under a binder (handles the bound name correctly)
substBind :: Subst name body
          => name -> body -> Bind name body -> Bind name body

-- The key insight: if substituting x, and binder binds x, do nothing
-- (the bound x shadows the outer x)
substBind x arg (Bind y body)
  | x == y    = Bind y body              -- Shadowed, no substitution
  | otherwise = Bind y (subst x arg body)
```

### Summary: Library vs User

| Component | Provider | Notes |
|-----------|----------|-------|
| `Nom`, `TyNom` | Library | Nominal atom types |
| `Bind`, `TyBind` | Library | Binder types with alpha-equiv |
| `freshNom`, `freshTyNom` | Library | Generate fresh names |
| `bind`, `bindTy` | Library | Create binders |
| `unbind`, `unbindTy` | Library | Open binders (generic) |
| `instantiate` | Library | Generic, uses `Subst` |
| `Subst` instance | **User** | Define for each syntax type |
| `LogicType` instance | **User** | Already required by TypedRedex |

---

## Example: Simply Typed Lambda Calculus

### Syntax

```haskell
module STLC.Syntax where

import TypedRedex
import TypedRedex.Nominal

-- Types
data Ty = TUnit | TArr Ty Ty
  deriving (Eq, Show)

-- Terms with named variables
data Tm
  = Var Nom                -- x
  | Unit                   -- ()
  | Lam Ty (Bind Nom Tm)   -- λx:A. e
  | App Tm Tm              -- e₁ e₂
  deriving (Eq, Show)

-- Contexts keyed by nominal atoms
data Ctx = Empty | Extend Nom Ty Ctx
  deriving (Eq, Show)

-- Smart constructors
var    :: LTerm Nom rel -> LTerm Tm rel
unit   :: LTerm Tm rel
lam    :: LTerm Ty rel -> LTerm (Bind Nom Tm) rel -> LTerm Tm rel
app    :: LTerm Tm rel -> LTerm Tm rel -> LTerm Tm rel

tunit  :: LTerm Ty rel
tarr   :: LTerm Ty rel -> LTerm Ty rel -> LTerm Ty rel

empty  :: LTerm Ctx rel
extend :: LTerm Nom rel -> LTerm Ty rel -> LTerm Ctx rel -> LTerm Ctx rel
```

### Subst Instance (Required for `instantiate`)

```haskell
instance Subst Nom Tm where
  subst x arg = go
    where
      go (Var y)
        | x == y    = arg
        | otherwise = Var y
      go Unit         = Unit
      go (Lam ty bnd) = Lam ty (substBind x arg bnd)
      go (App e1 e2)  = App (go e1) (go e2)
```

### Context Lookup

```haskell
-- Γ(x) = A
lookupCtx :: Redex rel => Judge rel '[Ctx, Nom, Ty]
lookupCtx = judgment "lookup" [here, there]
  where
    --  ─────────────────────────
    --  (Γ, x:A)(x) = A
    here = rule "lookup-here" $ do
      x <- freshNom
      [ty, rest] <- freshVars
      concl $ lookupCtx (extend x ty rest) x ty

    --       Γ(x) = A
    --  ─────────────────────────
    --  (Γ, y:B)(x) = A
    there = rule "lookup-there" $ do
      x <- freshNom
      y <- freshNom
      [tyX, tyY, rest] <- freshVars
      concl $ lookupCtx (extend y tyY rest) x tyX
      prem $ lookupCtx rest x tyX
```

### Typing Rules

```haskell
-- Γ ⊢ e : A
typeof :: Redex rel => Judge rel '[Ctx, Tm, Ty]
typeof = judgment "typeof" [typeofVar, typeofUnit, typeofLam, typeofApp]
  where
    --      Γ(x) = A
    --  ─────────────────
    --    Γ ⊢ x : A
    typeofVar = rule "T-Var" $ do
      x <- freshNom
      [ctx, ty] <- freshVars
      concl $ typeof ctx (var x) ty
      prem $ lookupCtx ctx x ty

    --  ─────────────────
    --   Γ ⊢ () : Unit
    typeofUnit = rule "T-Unit" $ do
      [ctx] <- freshVars
      concl $ typeof ctx unit tunit

    --     Γ, x:A ⊢ e : B
    --  ─────────────────────────
    --   Γ ⊢ λx:A. e : A → B
    typeofLam = rule "T-Lam" $ do
      [ctx, tyA, tyB, bnd] <- freshVars
      concl $ typeof ctx (lam tyA bnd) (tarr tyA tyB)
      -- Open the binder: get fresh name + body
      (x, body) <- unbind bnd
      prem $ typeof (extend x tyA ctx) body tyB

    --   Γ ⊢ e₁ : A → B    Γ ⊢ e₂ : A
    --  ─────────────────────────────────
    --         Γ ⊢ e₁ e₂ : B
    typeofApp = rule "T-App" $ do
      [ctx, e1, e2, tyA, tyB] <- freshVars
      concl $ typeof ctx (app e1 e2) tyB
      prem $ typeof ctx e1 (tarr tyA tyB)
      prem $ typeof ctx e2 tyA
```

### Operational Semantics

```haskell
-- Values
isValue :: Redex rel => Judge rel '[Tm]
isValue = judgment "value" [valUnit, valLam]
  where
    valUnit = rule "val-unit" $ concl $ isValue unit
    valLam = rule "val-lam" $ do
      [ty, bnd] <- freshVars
      concl $ isValue (lam ty bnd)

-- Small-step: e → e'
step :: Redex rel => Judge rel '[Tm, Tm]
step = judgment "step" [stepBeta, stepApp1, stepApp2]
  where
    --   value v
    --  ─────────────────────────
    --  (λx:A. e) v → [v/x]e
    stepBeta = rule "β" $ do
      [ty, bnd, v, result] <- freshVars
      concl $ step (app (lam ty bnd) v) result
      prem $ isValue v
      -- Capture-avoiding substitution via instantiate
      result' <- instantiate bnd v
      prem $ result === result'

    --      e₁ → e₁'
    --  ─────────────────────
    --   e₁ e₂ → e₁' e₂
    stepApp1 = rule "app₁" $ do
      [e1, e1', e2] <- freshVars
      concl $ step (app e1 e2) (app e1' e2)
      prem $ step e1 e1'

    --   value v    e₂ → e₂'
    --  ────────────────────────
    --     v e₂ → v e₂'
    stepApp2 = rule "app₂" $ do
      [v, e2, e2'] <- freshVars
      concl $ step (app v e2) (app v e2')
      prem $ isValue v
      prem $ step e2 e2'
```

---

## Example: System F

### Syntax

```haskell
module SystemF.Syntax where

import TypedRedex
import TypedRedex.Nominal

-- Types with ∀
data Ty
  = TVar TyNom                 -- α
  | TArr Ty Ty                 -- A → B
  | TForall (TyBind TyNom Ty)  -- ∀α. A
  deriving (Eq, Show)

-- Terms with Λ and type application
data Tm
  = Var Nom                    -- x
  | Lam Ty (Bind Nom Tm)       -- λx:A. e
  | App Tm Tm                  -- e₁ e₂
  | TyLam (TyBind TyNom Tm)    -- Λα. e
  | TyApp Tm Ty                -- e [A]
  deriving (Eq, Show)

-- Contexts with both term and type bindings
data Ctx
  = Empty
  | ExtendTm Nom Ty Ctx        -- Γ, x:A
  | ExtendTy TyNom Ctx         -- Γ, α
  deriving (Eq, Show)
```

### Subst Instances (Required for `instantiate`)

```haskell
-- Term substitution [e/x] in terms
instance Subst Nom Tm where
  subst x arg = go
    where
      go (Var y)
        | x == y    = arg
        | otherwise = Var y
      go (Lam ty bnd)   = Lam ty (substBind x arg bnd)
      go (App e1 e2)    = App (go e1) (go e2)
      go (TyLam bnd)    = TyLam (substBindTy x arg bnd)  -- x is term var, not type var
      go (TyApp e ty)   = TyApp (go e) ty

-- Type substitution [A/α] in types
instance Subst TyNom Ty where
  subst alpha arg = go
    where
      go (TVar beta)
        | alpha == beta = arg
        | otherwise     = TVar beta
      go (TArr a b)     = TArr (go a) (go b)
      go (TForall bnd)  = TForall (substBindTy alpha arg bnd)

-- Type substitution [A/α] in terms
instance Subst TyNom Tm where
  subst alpha arg = go
    where
      go (Var x)        = Var x
      go (Lam ty bnd)   = Lam (subst alpha arg ty) (substBind alpha arg bnd)
      go (App e1 e2)    = App (go e1) (go e2)
      go (TyLam bnd)    = TyLam (substBindTy alpha arg bnd)
      go (TyApp e ty)   = TyApp (go e) (subst alpha arg ty)
```

### Typing Rules for Polymorphism

```haskell
typeof :: Redex rel => Judge rel '[Ctx, Tm, Ty]
typeof = judgment "typeof" [..., typeofTyLam, typeofTyApp]
  where
    --     Γ, α ⊢ e : A
    --  ─────────────────────
    --   Γ ⊢ Λα. e : ∀α. A
    typeofTyLam = rule "T-TyLam" $ do
      [ctx, tyBnd, tmBnd] <- freshVars
      concl $ typeof ctx (tyLam tmBnd) (tforall tyBnd)
      -- Open both binders with same fresh type variable
      (alpha, body) <- unbindTy tmBnd
      (alpha', tyBody) <- unbindTy tyBnd
      prem $ alpha === alpha'  -- Must bind same variable
      prem $ typeof (extendTy alpha ctx) body tyBody

    --   Γ ⊢ e : ∀α. A
    --  ─────────────────────
    --   Γ ⊢ e [B] : [B/α]A
    typeofTyApp = rule "T-TyApp" $ do
      [ctx, e, tyArg, tyBnd, result] <- freshVars
      concl $ typeof ctx (tyApp e tyArg) result
      prem $ typeof ctx e (tforall tyBnd)
      -- Instantiate ∀ with type argument
      result' <- instantiateTy tyBnd tyArg
      prem $ result === result'
```

---

## Implementation Notes

### Alpha-Equivalence via Unification

When unifying `Bind a t` with `Bind b u`:
1. If `a == b`: unify `t` with `u` directly
2. If `a ≠ b`: swap `a ↔ b` in `u`, then unify `t` with the swapped result

This follows the alphaKanren σ-rules for tie unification.

### Implicit Freshness

The `unbind` operation:
1. Generates a fresh `Nom` via counter
2. Internally records freshness constraints (nabla in alphaKanren)
3. Returns the fresh name and opened body

Users never write explicit `hash` (freshness) constraints.

### Module Structure

```
TypedRedex/
├── Nominal/
│   ├── Nom.hs         -- Nom, TyNom types
│   ├── Bind.hs        -- Bind, TyBind with LogicType
│   ├── Permutation.hs -- Name swapping
│   └── Unify.hs       -- Nominal unification
└── Nominal.hs         -- Public API re-exports
```

---

## References

- [alphaKanren paper](http://webyrd.net/alphamk/alphamk.pdf) - Byrd & Friedman, WSFP 2007
- [alphaKanren source](https://github.com/webyrd/alphaKanren) - Reference implementation
- [Nominal Logic Programming](https://dl.acm.org/doi/10.1145/1387673.1387675) - Cheney & Urban, TOPLAS 2008
- [unbound library](https://hackage.haskell.org/package/unbound) - Haskell library for locally nameless
