# Binding Support for TypedRedex

## Final Implementation (TypedRedex.Binding)

The binding module is implemented in `TypedRedex.Binding` and provides locally nameless
representation with an unbound-generics-inspired API.

### Design Choices Made

1. **Internal representation**: Locally nameless with name hints
2. **User API**: Users write names, never see de Bruijn indices
3. **Alpha-equivalence**: Automatic in unification (via de Bruijn body comparison)
4. **Pattern matching**: Use `unbind` in rules to access binding contents

### Architecture

```
User writes:        bind "x" (fvar "x")
                         ↓ smart constructor converts FVar→BVar
Internal storage:   Bind (Name "x") (BVar 0)
                         ↓ unification compares de Bruijn bodies only
Alpha-equiv:        bind "x" (fvar "x") ≡ bind "y" (fvar "y")  ✓
                         ↓ unbind converts BVar→FVar
User sees:          name hint + body with FVar
```

### Core Types

```haskell
-- | Typed variable name (for display)
newtype Name a = Name { unName :: String }

-- | Locally nameless variable
data Var a = BVar Nat     -- Bound variable (de Bruijn index, internal)
           | FVar (Name a) -- Free variable (named, user-facing)

-- | Binding construct with automatic alpha-equivalence
data Bind p t = Bind p t
-- Alpha-equiv: unifyVal compares bodies only, ignoring name hints
```

### User-Facing API

```haskell
-- Create a name
mkName :: String -> Logic (Name a) var

-- Create a free variable (the primary way users create variables)
fvar :: String -> Logic (Var a) var
fvar s = Ground $ FVarR (Ground $ NameR s)

-- Create a binding (converts FVar→BVar for the bound name)
bind :: String -> Logic (Var a) var -> Logic (Bind (Name a) (Var a)) var
bind x body = Ground $ BindR (mkName x) (convertFVarToBVar x body)

-- Open a binding in a continuation (converts BVar→FVar)
unbind :: (Redex rel)
       => LTerm (Bind (Name a) (Var a)) rel
       -> (LTerm (Name a) rel -> LTerm (Var a) rel -> rel b)
       -> rel b
```

### Usage Example

```haskell
-- Define a term type using binding
data Tm
  = TmVar (Var Tm)           -- Variable
  | Lam (Bind (Name Tm) Tm)  -- Lambda with binding
  | App Tm Tm
  deriving (Generic)

-- Smart constructors for CONCRETE terms
var :: String -> LTerm Tm rel
var s = Ground $ TmVarR (fvar s)

lam :: String -> LTerm Tm rel -> LTerm Tm rel
lam x body = Ground $ LamR (bind x body)  -- converts FVar x → BVar 0

-- Pattern wrapper (for matching in rules, no conversion)
lamP :: LTerm (Bind (Name Tm) Tm) rel -> LTerm Tm rel
lamP bnd = Ground $ LamR bnd

-- Writing rules: use unbind for patterns
typeLam :: (Redex rel) => Rule rel '[Ctx, Tm, Ty]
typeLam = rule "type-lam" $ fresh4 $ \ctx a b bnd -> do
  concl $ typeof ctx (lamP bnd) (tarr a b)    -- lamP for pattern
  prem  $ unbind bnd $ \x body ->              -- unbind to access
    typeof (extend ctx x a) body b

-- Beta reduction
stepBeta :: (Redex rel) => Rule rel '[Tm, Tm]
stepBeta = rule "beta" $ fresh3 $ \bnd arg result -> do
  concl $ step (app (lamP bnd) arg) result    -- lamP for pattern
  prem  $ unbind bnd $ \x body ->              -- unbind to get x, body
    subst x arg body result

-- Concrete terms use lam (auto-converts FVar→BVar)
idTm = lam "x" (var "x")               -- λx. x
constTm = lam "x" (lam "y" (var "x"))  -- λx. λy. x

-- Alpha-equivalence works automatically in unification
-- lam "x" (var "x") unifies with lam "y" (var "y")  ✓
```

### Pattern vs Term Construction

| Context | Use | Behavior |
|---------|-----|----------|
| Concrete term | `lam "x" body` | Converts FVar→BVar |
| Rule pattern | `lamP bnd` + `unbind bnd $ \x body -> ...` | No conversion, extracts via unbind |

### Internal Details (Hidden from Users)

- `Nat` type for de Bruijn indices: `Z | S Nat`
- `bvar :: Logic Nat var -> Logic (Var a) var` - internal, creates BVar
- `zro`, `suc` - internal nat constructors
- `convertFVarToBVar` - converts matching FVar to BVar 0
- `convertBVarToFVar` - converts BVar 0 back to FVar with name hint

### Limitations / Future Work

- `bind` only works correctly for simple `Var` bodies; nested terms need recursive conversion
- Helper relations (`nameEq`, `nameNeq`, `freeIn`) not yet implemented
- Generic `subst` not provided; users write their own using `unbind`

---

# Original Proposals (Historical Reference)

## Design Goals

1. **Program with names** — Write `λx. x`, not `λ. 0`
2. **Consistent code ↔ pretty-print** — What you write is what you see
3. **Simple API** — Inspired by unbound-generics: `bind`, `unbind`, `aeq`, `subst`
4. **Relational** — Works bidirectionally in miniKanren-style logic programming

---

## Original Situation

TypedRedex originally used raw de Bruijn indices:

```haskell
data Tm = Var Nat | Lam Tm | App Tm Tm  -- de Bruijn

-- User must write:
ex = Lam (Lam (Var (S Z)))  -- λ. λ. 1  (meaning λx. λy. x)

-- Pretty-prints as numbers, not names
```

**Problems:**
1. Writing `Var (S (S Z))` is error-prone and unreadable
2. Manual shifting for substitution
3. Pretty-print shows indices, not names — inconsistent with how humans think

---

## Proposal A: Named Representation with Auto-Conversion (Recommended)

**Core Idea:** Users write with names. The library automatically converts to de Bruijn for unification (alpha-equivalence) and back to names for display.

### User-Facing API

```haskell
-- Names are first-class
type Name = String

-- User-facing term type (what they write)
data Tm
  = Var Name
  | Lam Name Tm        -- λx. body
  | App Tm Tm
  deriving (Show, Generic)

-- Smart constructors for logic terms
var :: Name -> LTerm Tm rel
lam :: Name -> LTerm Tm rel -> LTerm Tm rel
app :: LTerm Tm rel -> LTerm Tm rel -> LTerm Tm rel

-- Example: identity function
idTm :: LTerm Tm rel
idTm = lam "x" (var "x")  -- Write exactly λx.x

-- Example: Church encoding
church2 :: LTerm Tm rel
church2 = lam "s" (lam "z" (app (var "s") (app (var "s") (var "z"))))
```

### Under the Hood: Locally Nameless

Internally, terms use locally nameless representation:

```haskell
-- Internal representation (hidden from user)
data TmInternal
  = BVar Nat           -- Bound variable (de Bruijn index)
  | FVar Name          -- Free variable (name)
  | LamI TmInternal    -- No name stored in binder
  | AppI TmInternal TmInternal

-- Conversion happens automatically
toInternal :: Tm -> TmInternal
fromInternal :: [Name] -> TmInternal -> Tm  -- needs name supply
```

### Alpha-Equivalence (Free!)

```haskell
-- Because internal rep is locally nameless:
λx.x  →  Lam (BVar 0)
λy.y  →  Lam (BVar 0)  -- Same!

-- Unification just works on the internal representation
```

### Pretty Printing (Consistent!)

```haskell
-- Uses the SAME names the user provided (when available)
-- Or generates fresh names x₀, x₁, ... when needed

prettyTm :: Tm -> String
prettyTm (Lam x body) = "λ" ++ x ++ ". " ++ prettyTm body
prettyTm (Var x) = x
prettyTm (App f a) = "(" ++ prettyTm f ++ " " ++ prettyTm a ++ ")"

-- λx. λy. x  prints as  "λx. λy. x"  ✓
```

### Integration with LogicType

```haskell
instance LogicType Tm where
  -- Reified stores the INTERNAL (locally nameless) representation
  -- but also remembers original names for pretty-printing
  data Reified Tm var = TmR
    { tmInternal :: TmInternal' var  -- for unification
    , tmNames    :: [Name]           -- for display
    }

  -- Unification works on internal rep (alpha-equiv is free)
  unifyVal unif (TmR i1 _) (TmR i2 _) = unifyInternal unif i1 i2

  -- Quote reconstructs named form for display
  quote (TmR internal names) = reconstructNamed internal names
```

### Substitution as a Relation

```haskell
-- subst x arg body result
-- Substitute arg for free occurrences of x in body
subst :: (Redex rel) => Judge rel '[Name, Tm, Tm, Tm]
subst = judgment "subst" [substVar, substVarNeq, substLam, substApp]
  where
    substVar = rule "subst-var" $ fresh2 $ \x arg ->
      concl $ subst x arg (var x) arg

    substVarNeq = rule "subst-var-neq" $ fresh3 $ \x y arg -> do
      concl $ subst x arg (var y) (var y)
      prem  $ nameNeq x y

    substLam = rule "subst-lam" $ fresh4 $ \x arg y body result -> do
      concl $ subst x arg (lam y body) (lam y result)
      prem  $ nameNeq x y           -- Barendregt: x ≠ y
      prem  $ notFreeIn y arg       -- Barendregt: y ∉ FV(arg)
      prem  $ subst x arg body result

    substApp = rule "subst-app" $ fresh5 $ \x arg f a f' a' -> do
      concl $ subst x arg (app f a) (app f' a')
      prem  $ subst x arg f f'
      prem  $ subst x arg a a'
```

### Example: Beta Reduction

```haskell
-- (λx. body) arg  →  [arg/x]body
stepBeta :: (Redex rel) => Judge rel '[Tm, Tm]
stepBeta = rule "β" $ fresh4 $ \x body arg result -> do
  concl $ step (app (lam x body) arg) result
  prem  $ subst x arg body result

-- Usage:
-- step (app (lam "x" (var "x")) (var "y")) ?result
-- yields: ?result = var "y"
```

### Pros
- **User writes names** — natural and readable
- **Pretty-print matches code** — `λx. x` stays `λx. x`
- **Alpha-equivalence is free** — via internal locally nameless
- **Moderate complexity** — conversion is mechanical

### Cons
- Need to maintain name↔index mapping
- Free variable names must be distinct from bound (Barendregt)

---

## Proposal B: Explicit Bind/Unbind Operations (unbound-style)

**Core Idea:** Provide `Bind` type and `unbind` relation, closely mirroring unbound-generics but in a relational setting.

### User-Facing API

```haskell
-- Names are logic terms
newtype Name a = Name String
  deriving (Eq, Show, Generic)

-- Bind wraps a binder scope
data Bind p t  -- p = pattern (what's bound), t = body

-- User-facing terms
data Tm
  = Var (Name Tm)
  | Lam (Bind (Name Tm) Tm)  -- λx. body
  | App Tm Tm
  deriving (Generic)

-- Smart constructors
var :: String -> LTerm Tm rel
var s = Ground $ VarR (Ground $ NameR s)

lam :: String -> LTerm Tm rel -> LTerm Tm rel
lam x body = Ground $ LamR (bind (name x) body)

-- Like unbound's bind/unbind, but as relations
bind :: LTerm (Name Tm) rel -> LTerm Tm rel -> LTerm (Bind (Name Tm) Tm) rel
unbind :: (Redex rel) => LTerm (Bind (Name Tm) Tm) rel
       -> (LTerm (Name Tm) rel -> LTerm Tm rel -> rel a) -> rel a
```

### Using unbind in Rules

```haskell
-- Γ, x:A ⊢ e : B
-- ─────────────────────
-- Γ ⊢ λx.e : A → B
typeLam = rule "type-lam" $ fresh3 $ \ctx a b -> fresh $ \bnd ->
  unbind bnd $ \x body -> do
    concl $ typeof ctx (lam' bnd) (tarr a b)
    prem  $ typeof (extend ctx x a) body b

-- Beta reduction
stepBeta = rule "β" $ fresh2 $ \arg result -> fresh $ \bnd ->
  unbind bnd $ \x body -> do
    concl $ step (app (lam' bnd) arg) result
    prem  $ subst x arg body result
```

### The unbind Operation

```haskell
-- unbind opens a binder, generating fresh names
unbind :: (Redex rel)
       => LTerm (Bind (Name a) t) rel
       -> (LTerm (Name a) rel -> LTerm t rel -> rel b)
       -> rel b
unbind bnd k = freshName $ \x -> fresh $ \body -> do
  -- open bnd with fresh x, get body
  openBind bnd x body
  k x body
```

### Alpha-Equivalence

```haskell
-- Two Binds are alpha-equivalent if opening with same fresh name gives equal bodies
aeq :: (Redex rel) => Judge rel '[Tm, Tm]
aeq = judgment "aeq" [aeqVar, aeqLam, aeqApp]
  where
    aeqLam = rule "aeq-lam" $ fresh2 $ \bnd1 bnd2 ->
      unbind2 bnd1 bnd2 $ \x body1 body2 -> do
        concl $ aeq (lam' bnd1) (lam' bnd2)
        prem  $ aeq body1 body2
```

### Pros
- Very close to unbound-generics API
- Explicit scope management
- Clean separation of binding

### Cons
- Slightly more verbose
- Need fresh name generation in logic monad

---

## Proposal C: Name Supply via Monad (Simplest)

**Core Idea:** Just use named terms everywhere. Track used names to avoid capture.

### User-Facing API

```haskell
data Tm
  = Var String
  | Lam String Tm
  | App Tm Tm
  deriving (Eq, Show, Generic)

-- Direct smart constructors
var :: String -> LTerm Tm rel
lam :: String -> LTerm Tm rel -> LTerm Tm rel
app :: LTerm Tm rel -> LTerm Tm rel -> LTerm Tm rel

-- Write terms naturally
idTm = lam "x" (var "x")
constTm = lam "x" (lam "y" (var "x"))
```

### LogicType Instance (Direct)

```haskell
instance LogicType Tm where
  data Reified Tm var
    = VarR String
    | LamR String (Logic Tm var)
    | AppR (Logic Tm var) (Logic Tm var)

  -- Unification is STRUCTURAL (not alpha-equiv!)
  unifyVal _ (VarR x) (VarR y) = guard (x == y)
  unifyVal unif (LamR x b) (LamR y b') = guard (x == y) >> unif b b'
  ...
```

### Alpha-Equivalence as Explicit Relation

```haskell
-- Must define alpha-equiv explicitly since unification is structural
alphaEq :: (Redex rel) => Judge rel '[Tm, Tm]
alphaEq = judgment "alphaEq" [aeqVar, aeqLam, aeqApp]
  where
    aeqLam = rule "aeq-lam" $ fresh4 $ \x y body1 body2 ->
      freshName $ \z -> fresh2 $ \body1' body2' -> do
        concl $ alphaEq (lam x body1) (lam y body2)
        prem  $ rename x z body1 body1'
        prem  $ rename y z body2 body2'
        prem  $ alphaEq body1' body2'
```

### Substitution with Freshening

```haskell
-- Must freshen to avoid capture
substFresh :: (Redex rel) => Judge rel '[String, Tm, Tm, Tm]
substFresh = judgment "subst" [...]
  where
    substLam = rule "subst-lam" $ fresh4 $ \x arg y body ->
      freshName $ \z -> fresh2 $ \body' result' -> do
        concl $ substFresh x arg (lam y body) (lam z result')
        prem  $ rename y z body body'           -- freshen bound var
        prem  $ substFresh x arg body' result'
```

### Pros
- **Simplest to implement**
- **User writes names directly**
- **Pretty-print is trivial** — just show the names

### Cons
- **Alpha-equiv not free** — must be explicit relation
- **Substitution more complex** — needs freshening
- **Unification is structural** — `λx.x ≠ λy.y` without explicit alpha

---

## Comparison

| Feature | Proposal A (Auto-Convert) | Proposal B (Bind/Unbind) | Proposal C (Named Direct) |
|---------|---------------------------|--------------------------|---------------------------|
| User writes | `lam "x" (var "x")` | `lam "x" body` | `lam "x" (var "x")` |
| Pretty-print | Names (consistent) ✓ | Names (consistent) ✓ | Names (consistent) ✓ |
| Alpha-equiv | Free (via internal DB) | Free (via unbind) | Explicit relation |
| Substitution | Relation on names | Relation with unbind | Relation with freshening |
| Implementation | Medium | Medium | Simple |
| API style | Transparent conversion | Like unbound-generics | Direct/raw |

---

## Recommendation

**A hybrid of Proposal A and B was implemented** as `TypedRedex.Binding`:

1. Uses locally nameless internally (like Proposal A)
2. Provides explicit `Bind`/`unbind` API (like Proposal B)
3. Alpha-equivalence is automatic via `Bind`'s `unifyVal`
4. Users write with names, never see de Bruijn indices

See the "Final Implementation" section at the top of this document for the actual API.

---

## Appendix: unbound-generics Key APIs (Reference)

```haskell
-- From unbound-generics that we want to emulate:

-- Types
Name a          -- Typed variable name
Bind p t        -- Binding: pattern p scopes over term t
Embed t         -- Embed term in pattern position

-- Operations
bind    :: p -> t -> Bind p t           -- Create binding
unbind  :: Bind p t -> Fresh m => m (p, t)  -- Open with fresh names
aeq     :: Alpha a => a -> a -> Bool    -- Alpha-equivalence
subst   :: Subst b a => Name b -> b -> a -> a  -- Substitution

-- Example from unbound LC.hs:
data Exp = Var (Name Exp)
         | Lam (Bind (Name Exp) Exp)
         | App Exp Exp

lam x body = Lam (bind x body)

-- Beta reduction:
red (App (Lam bnd) arg) = do
  (x, body) <- unbind bnd
  return $ subst x arg body
```

For TypedRedex, we adapt these to work relationally:

```haskell
-- TypedRedex versions:
bind   :: LTerm (Name a) rel -> LTerm t rel -> LTerm (Bind (Name a) t) rel
unbind :: LTerm (Bind (Name a) t) rel -> ((Name, t) -> rel a) -> rel a
aeq    :: Judge rel '[a, a]  -- Alpha-equiv as a relation (or implicit via unification)
subst  :: Judge rel '[Name a, a, t, t]  -- Substitution as a relation
```
