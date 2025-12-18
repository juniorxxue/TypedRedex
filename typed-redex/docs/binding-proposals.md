# Binding Representation Proposals for TypedRedex (Revised)

## Design Goals

1. **Program with names** — Write `λx. x`, not `λ. 0`
2. **Consistent code ↔ pretty-print** — What you write is what you see
3. **Simple API** — Inspired by unbound-generics: `bind`, `unbind`, `aeq`, `subst`
4. **Relational** — Works bidirectionally in miniKanren-style logic programming

---

## Current Situation

TypedRedex uses raw de Bruijn indices:

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

**Proposal A (Auto-Convert)** offers the best balance:

1. **Cleanest user experience** — write `lam "x" (var "x")`, get `λx. x`
2. **Alpha-equiv is automatic** — unification handles it
3. **Pretty-print is consistent** — preserves user's names
4. **Hidden complexity** — de Bruijn is internal detail

### Implementation Sketch

```haskell
-- Module: TypedRedex.Binding.Named

-- | Named term with original names preserved
data Named a = Named
  { namedValue :: a        -- Original named term
  , namedDB    :: DB a     -- De Bruijn version (for unification)
  }

-- | LogicType instance handles conversion transparently
instance LogicType (Named Tm) where
  -- Unification compares de Bruijn forms
  unifyVal unif (NamedR _ db1) (NamedR _ db2) = unifyDB unif db1 db2

  -- Quote reconstructs named form
  quote (NamedR named _) = quoteNamed named

-- | User-facing smart constructors
lam :: (Redex rel) => String -> LTerm Tm rel -> LTerm Tm rel
lam x body = wrapNamed (Lam x (unwrapNamed body))

-- | The magic: consistent names in, consistent names out
-- User writes: lam "x" (lam "y" (var "x"))
-- Unifies:     as Lam (Lam (BVar 1))
-- Displays:    λx. λy. x
```

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
