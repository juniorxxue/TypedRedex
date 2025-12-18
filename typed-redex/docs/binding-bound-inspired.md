# Binding Support: Bound-Inspired Design

## What We Learned from `bound`

The `bound` library by Edward Kmett uses:

1. **`Var b a`** - Either bound (`B b`) or free (`F a`) variable
2. **`Scope b f a`** - Wraps `f (Var b (f a))` for binding
3. **`abstract`** - Captures free vars: `(a -> Maybe b) -> f a -> Scope b f a`
4. **`instantiate`** - Opens scope: `(b -> f a) -> Scope b f a -> f a`
5. **Monad instances** - Substitution via `>>=`

Key insight: **Alpha-equivalence is free** because same de Bruijn = same term.

## Why We Can't Use Bound Directly

1. Bound assumes terms are Monads (substitution = monadic bind)
2. TypedRedex uses LogicType (unification-based, relational)
3. Bound's `abstract`/`instantiate` are pure functions on concrete terms
4. TypedRedex needs to handle logic variables in terms

## Proposed Adaptation

### Option 1: Simplest De Bruijn (Recommended)

Just use de Bruijn indices with name annotations. No Var type needed in the term itself.

```haskell
-- User's term type
data Tm
  = TmVar Int         -- de Bruijn index
  | Lam String Tm     -- λ with name hint + body
  | App Tm Tm

-- LogicType: alpha-equiv ignores name hints
instance LogicType Tm where
  unifyVal unif (LamR _ b1) (LamR _ b2) = unif b1 b2  -- ignore name!
  unifyVal unif (TmVarR n) (TmVarR m) = unif n m
  unifyVal unif (AppR f1 a1) (AppR f2 a2) = unif f1 f2 >> unif a1 a2
  unifyVal _ _ _ = empty
```

**Smart constructors** (for building concrete terms):

```haskell
-- Convert name → de Bruijn at construction time
lam :: String -> Tm -> Tm
lam x body = Lam x (abstract x 0 body)
  where
    abstract :: String -> Int -> Tm -> Tm
    abstract x n (TmVar i) = TmVar i  -- already de Bruijn
    abstract x n (Lam y b) = Lam y (abstract x (n+1) b)
    abstract x n (App f a) = App (abstract x n f) (abstract x n a)

-- For building terms with names that get converted
var :: String -> Tm
-- This needs a different approach - see below
```

**Problem**: The `var` smart constructor can't work standalone because we don't know the de Bruijn index until we're inside a `lam`.

**Solution**: Use a builder monad or different term type for construction:

```haskell
-- Named term type (for writing)
data NTm = NVar String | NLam String NTm | NApp NTm NTm

-- Convert named → de Bruijn
toDebruijn :: NTm -> Tm
toDebruijn = go []
  where
    go env (NVar x) = case elemIndex x env of
      Just i  -> TmVar i
      Nothing -> error $ "unbound: " ++ x
    go env (NLam x b) = Lam x (go (x:env) b)
    go env (NApp f a) = App (go env f) (go env a)

-- Smart constructors build NTm, then convert
lam :: String -> NTm -> NTm
lam = NLam

var :: String -> NTm
var = NVar

app :: NTm -> NTm -> NTm
app = NApp

-- Final conversion for ground terms
term :: NTm -> LTerm Tm var
term = Ground . project . toDebruijn
```

**Pros**:
- Very simple representation
- Alpha-equiv automatic
- Clean separation: NTm for writing, Tm for computation

**Cons**:
- Two term types
- Ground terms only for smart constructors

### Option 2: Locally Nameless (Current Approach, Refined)

Keep `Var = BVar Nat | FVar Name` but simplify:

```haskell
data Tm
  = TmVar (Var Tm)           -- BVar or FVar
  | Lam (Name Tm) Tm         -- Name hint + body (body uses BVar 0)
  | App Tm Tm

-- Smart constructor
lam :: String -> Tm -> Tm
lam x body = Lam (Name x) (abstract x 0 body)
  where
    abstract x n (TmVar (FVar (Name y)))
      | x == y    = TmVar (BVar (intToNat n))
      | otherwise = TmVar (FVar (Name y))
    abstract x n (TmVar (BVar i)) = TmVar (BVar i)
    abstract x n (Lam h b) = Lam h (abstract x (n+1) b)
    abstract x n (App f a) = App (abstract x n f) (abstract x n a)

-- Opening a binder (pure function)
instantiate :: Tm -> Tm -> Tm
instantiate arg body = go 0 body
  where
    go n (TmVar (BVar i))
      | natToInt i == n = arg
      | natToInt i > n  = TmVar (BVar (intToNat (natToInt i - 1)))
      | otherwise       = TmVar (BVar i)
    go n (TmVar (FVar x)) = TmVar (FVar x)
    go n (Lam h b) = Lam h (go (n+1) b)
    go n (App f a) = App (go n f) (go n a)
```

**For TypedRedex rules**: Pattern match, then use instantiate:

```haskell
stepBeta :: Judge rel '[Tm, Tm]
stepBeta = rule "beta" $ fresh3 $ \nameHint body arg -> do
  concl $ step (app (lamP nameHint body) arg) (instantiate arg body)
  -- lamP is pattern-only constructor, doesn't do abstraction
```

### Option 3: Named + Explicit Substitution Relation

This is Option B from the revised proposals. Keep named terms, define substitution as a relation:

```haskell
data Tm = TmVar String | Lam String Tm | App Tm Tm

-- Structural unification (NOT alpha-equiv)
instance LogicType Tm where
  unifyVal unif (TmVarR x) (TmVarR y) = unif x y
  unifyVal unif (LamR x b) (LamR y b') = unif x y >> unif b b'
  ...

-- Alpha-equivalence as explicit relation
alphaEq :: Judge rel '[Tm, Tm]

-- Substitution as explicit relation
subst :: Judge rel '[String, Tm, Tm, Tm]  -- subst x e t result = [e/x]t
```

## Recommendation

**For TypedRedex, I recommend Option 1 (Simple De Bruijn) with two term types**:

1. `NTm` - Named terms for writing (with smart constructors)
2. `Tm` - De Bruijn terms for computation (with LogicType)

This is essentially what PLT Redex does internally, and what bound does too (just more implicitly via the type parameter).

**Rationale**:
- Simplest implementation
- Alpha-equivalence automatic and correct
- Clear separation of concerns
- No complex typeclass machinery
- Works perfectly with LogicType/unification

**Implementation Plan**:

1. Define `NTm` type with named smart constructors
2. Define `Tm` type with de Bruijn representation
3. Write `toDebruijn :: NTm -> Tm` conversion
4. Write LogicType instance for `Tm` with alpha-equiv
5. Provide `term :: NTm -> LTerm Tm var` combinator
6. Provide `instantiate :: Tm -> Tm -> Tm` for opening binders

## Example Usage

```haskell
-- Building terms (uses NTm internally)
idTm :: LTerm Tm var
idTm = term $ lam "x" (var "x")

constTm :: LTerm Tm var
constTm = term $ lam "x" (lam "y" (var "x"))

-- Alpha-equivalence works automatically
-- idTm unifies with: term $ lam "y" (var "y")

-- Writing rules
typeofLam :: Judge rel '[Ctx, Tm, Ty]
typeofLam = rule "typeof-lam" $ fresh4 $ \ctx x body tyB -> do
  concl $ typeof ctx (lamP x body) (tarr tyA tyB)
  -- x is the name hint (for display)
  -- body is de Bruijn body (BVar 0 = bound var)
  prem $ typeof (extendCtx ctx tyA) body tyB  -- context uses index, not name

-- Beta reduction
stepBeta :: Judge rel '[Tm, Tm]
stepBeta = rule "beta" $ fresh3 $ \h body arg -> do
  concl $ step (app (lamP h body) arg) (instantiateTm arg body)
  -- instantiateTm is a helper that substitutes arg for BVar 0
```

## Multi-Sorted Binding (System F)

For System F with both term and type binding:

```haskell
-- Separate named types for writing
data NTy = NTVar String | NTArr NTy NTy | NTAll String NTy
data NTm = NVar String | NLam String NTy NTm | NApp NTm NTm
         | NTLam String NTm | NTApp NTm NTy

-- Separate de Bruijn types for computation
data Ty = TVar Int | TArr Ty Ty | TAll String Ty
data Tm = Var Int | Lam String Ty Tm | App Tm Tm | TLam String Tm | TApp Tm Ty

-- Separate conversion functions
toDebruijnTy :: [String] -> NTy -> Ty
toDebruijnTm :: [String] -> [String] -> NTm -> Tm  -- type env, term env
```

This scales naturally to any number of binding sorts.
