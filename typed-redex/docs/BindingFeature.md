# Nominal Logic Binding Features in TypedRedex

This document describes the implementation of alphaKanren-style nominal logic for handling lambda bindings with named variables in TypedRedex.

## Motivation

Traditional approaches to variable binding in type systems use de Bruijn indices, which avoid naming issues but make terms harder to read and manipulate. Nominal logic provides an alternative: use explicit names with built-in support for alpha-equivalence.

The key insight from alphaKanren: treat binders as opaque structures where alpha-equivalent terms unify automatically.

```
Bind x (Var x)  ≡  Bind y (Var y)   -- alpha-equivalent, should unify
```

## Core Types

### NominalAtom Typeclass

The `NominalAtom` typeclass defines the requirements for a name type:

```haskell
class (Eq name, LogicType name) => NominalAtom name where
  swapAtom :: name -> name -> name -> name
```

Any type that implements `NominalAtom` can be used with `Bind`.

### Provided Atom Types

```haskell
newtype Nom = Nom Int      -- Term variable names
newtype TyNom = TyNom Int  -- Type variable names
```

### Generic Binder

```haskell
data Bind name body = Bind !name body
```

The `Bind` type is parameterized by:
- `name`: The type of nominal atom (must be a `NominalAtom`)
- `body`: The type of the body

Examples:
```haskell
Bind Nom Tm        -- term binder (lambda)
Bind TyNom Ty      -- type binder (forall)
Bind KindNom Kind  -- kind binder (if you need one)
```

## Alpha-Equivalence in Unification

The `LogicType` instance for `Bind` implements alpha-equivalence directly in `unifyVal`:

```haskell
unifyVal unif (BindR a1 b1) (BindR a2 b2) =
  case (reify a1, reify a2) of
    (Just n1, Just n2)
      | n1 == n2  -> unif b1 b2           -- Same name: unify bodies directly
      | otherwise -> case (b1, b2) of
          (_, Ground br2) ->               -- Swap n1↔n2 in b2, then unify
            let swapped = swap n1 n2 (reify br2)
            in unif b1 (Ground (project swapped))
          (Ground br1, Free _) ->          -- Swap n2↔n1 in b1, then unify
            let swapped = swap n2 n1 (reify br1)
            in unif (Ground (project swapped)) b2
          (Free _, Free _) ->              -- Both variables: unify directly
            unif b1 b2
```

### The Permute Typeclass

The `Permute` typeclass defines name swapping:

```haskell
class Permute name term where
  swap :: name -> name -> term -> term
```

`NominalAtom` instances automatically get a self-swap via `swapAtom`.

## High-Level API

### Generic Operations

```haskell
-- Open a binder with a custom fresh name generator
unbindWith :: (forall a. (name -> rel a) -> rel a)
           -> LTerm (Bind name body) rel
           -> rel (LTerm name rel, LTerm body rel)

-- Instantiate (substitute) a binder
instantiate :: LTerm (Bind name body) rel
            -> LTerm body rel
            -> rel (LTerm body rel)

-- Instantiate and unify with result
instantiateTo :: LTerm (Bind name body) rel
              -> LTerm body rel
              -> LTerm body rel
              -> rel ()
```

### Specialized Operations (for Nom and TyNom)

```haskell
unbind   :: LTerm (Bind Nom body) rel -> rel (LTerm Nom rel, LTerm body rel)
unbindTy :: LTerm (Bind TyNom body) rel -> rel (LTerm TyNom rel, LTerm body rel)
```

### Smart Constructors

```haskell
-- Create a binder (works with any NominalAtom)
bind :: name -> LTerm body rel -> LTerm (Bind name body) rel

-- Create ground name references
nom :: Nom -> LTerm Nom rel
tynom :: TyNom -> LTerm TyNom rel
```

## Usage Example: System F Type Checker

### Syntax Definition

```haskell
data Ty
  = TUnit
  | TVar TyNom
  | TArr Ty Ty
  | TAll (Bind TyNom Ty)    -- forall alpha. A

data Tm
  = Unit
  | Var Nom
  | Lam Ty (Bind Nom Tm)    -- lambda x:A. e
  | App Tm Tm
  | TLam (Bind TyNom Tm)    -- Lambda alpha. e
  | TApp Tm Ty              -- e [A]
```

### Typing Rules

```haskell
typeof :: Judge rel '[Ctx, Tm, Ty]
typeof = judgment "typeof" [typeofUnit, typeofVar, typeofLam, typeofApp, typeofTLam, typeofTApp]
  where
    -- Gamma, x:A |- e : B  =>  Gamma |- lam x:A. e : A -> B
    typeofLam = rule "typeof-lam" $ fresh2 $ \ctx tyA -> do
      freshNom_ $ \x -> fresh2 $ \body tyB -> do
        concl $ typeof ctx (lam tyA (bind x body)) (tarr tyA tyB)
        prem  $ typeof (tmBind (nom x) tyA ctx) body tyB

    -- Gamma, alpha |- e : A  =>  Gamma |- Lam alpha. e : forall alpha. A
    typeofTLam = rule "typeof-tlam" $ fresh $ \ctx -> do
      freshTyNom_ $ \alpha -> fresh2 $ \body tyBody -> do
        concl $ typeof ctx (tlam (bind alpha body)) (tall (bind alpha tyBody))
        prem  $ typeof (tyBind' (tynom alpha) ctx) body tyBody

    -- Gamma |- e : forall alpha. A  =>  Gamma |- e [B] : A[alpha := B]
    typeofTApp = rule "typeof-tapp" $ fresh5 $ \ctx e tyArg tyBnd result -> do
      concl $ typeof ctx (tapp e tyArg) result
      prem  $ typeof ctx e (tall tyBnd)
      instantiateTo tyBnd tyArg result
```

## Adding a New Name Type

To add a third kind of name (e.g., for kind variables):

### 1. Define the name type

```haskell
newtype KindNom = KindNom Int
  deriving (Eq, Ord)

instance Show KindNom where
  show (KindNom n) = "κ" ++ show n

instance NominalAtom KindNom

-- LogicType instance (similar to Nom/TyNom)
instance LogicType KindNom where
  data Reified KindNom var = KindNomR Int
  project (KindNom n) = KindNomR n
  reify (KindNomR n) = Just (KindNom n)
  -- ... rest of instance
```

### 2. Add fresh name generation

```haskell
-- In your interpreter state, add a counter
data MyState = MyState { ..., nextKindNom :: Int }

-- Provide a fresh generator
freshKindNom_ :: (KindNom -> rel a) -> rel a
freshKindNom_ k = do
  s <- get
  let n = nextKindNom s
  put s { nextKindNom = n + 1 }
  k (KindNom n)
```

### 3. Implement Permute instances

```haskell
instance Permute KindNom Kind where
  swap a b k = ... -- traverse Kind, swapping KindNom values

-- Cross-namespace (no effect)
instance Permute KindNom Ty where
  swap _ _ ty = ty

instance Permute KindNom Tm where
  swap _ _ tm = tm
```

### 4. Implement Subst instance (if needed)

```haskell
instance Subst KindNom Kind where
  subst name replacement kind = ...
```

### 5. Use with Bind

```haskell
data Kind = KStar | KArr Kind Kind | KAll (Bind KindNom Kind)

-- In rules, use unbindWith with your fresh generator
(kappa, body) <- unbindWith freshKindNom_ bnd
```

## Module Structure

```
TypedRedex/
├── Nominal.hs              -- Public API (re-exports)
└── Nominal/
    ├── Nom.hs              -- NominalAtom, Nom, TyNom
    ├── Bind.hs             -- Bind, Permute, LogicType instance
    └── Subst.hs            -- Subst typeclass
```

## Required Instances for Custom Syntax

To use nominal features with your own syntax types, implement:

```haskell
-- Permute instances for name swapping
instance Permute Nom MyTerm where
  swap a b term = ...

instance Permute TyNom MyType where
  swap a b ty = ...

-- Subst instance for substitution
instance Subst TyNom MyType where
  subst name replacement ty = ...
```

## Summary

The nominal logic implementation provides:

1. **Generic binders** — `Bind name body` works with any `NominalAtom` type
2. **Automatic alpha-equivalence** — Built into unification via `Permute`
3. **Extensibility** — Add new name types by implementing `NominalAtom` and a fresh generator
4. **Clean API** — `unbind`, `instantiate`, `bind` work generically
5. **Specialized helpers** — `unbindTy`, `instantiateTyTo` for common cases

The key design principle: binders are opaque, and alpha-equivalent terms unify automatically through the `Permute` (swap) mechanism in `unifyVal`.
