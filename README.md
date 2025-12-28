# TypedRedex: A typed embedding of PLT Redex in haskell

## Negation

```
neg $ do { x <- fresh; prem $ foo x } — Full rule DSL inside negation, most flexible.
```

This case is inspiring, since we want negation not only in a function that returns just book (checking function), sometimes we wish the follow statement to negate a function with outputs.
Theoretical challenges in execution and static mode-checking?

```
neg $ {x <- fresh; prem $ infer e x} 
```

# Free Monad Approach

## Overview

A typed DSL for defining inference rules with:
- **User DSL** — do-notation syntax for writing rules
- **Pure AST** — Free monad indexed with compile-time mode checking
- **Multiple Interpreters** — Typeset, Eval, Trace

```
┌─────────────────────────────────────────────────────────────┐
│              User DSL (do-notation)                         │
│   fresh, concl, prem, (===), (=/=), neg                     │
└─────────────────────────────────────────────────────────────┘
                           │
                           ▼
┌─────────────────────────────────────────────────────────────┐
│              Free Monad AST (Pure)                          │
│   RuleF, Term, Logic — indexed types, mode-checked          │
│   Serializable, inspectable, backend-agnostic               │
└─────────────────────────────────────────────────────────────┘
                           │
         ┌─────────────────┼─────────────────┐
         │                 │                 │
         ▼                 ▼                 ▼
┌─────────────┐    ┌─────────────┐    ┌─────────────┐
│  Typeset    │    │    Eval     │    │   Trace     │
│ Interpreter │    │ Interpreter │    │ Interpreter │
└─────────────┘    └─────────────┘    └─────────────┘
         │                 │                 │
         ▼                 ▼                 ▼
     LaTeX/Text      miniKanren AST     Derivation Tree
                           │                 │
                           ▼                 ▼
                       Results ◄─────────────┘
```

---

## User-Facing API

### Judgment Definition

```haskell
isEvar :: Judgment "isEvar" '[I, I] '[Env, TyNom]
isEvar = judgment $ \rule ->
  [ rule "here" $ do
      (a, env) <- fresh2
      concl $ isEvar (eevar a env) a

  , rule "there-eevar" $ do
      (a, b, env) <- fresh3
      a =/= b
      prem  $ isEvar env a
      concl $ isEvar (eevar b env) a
  ]

synth :: Judgment "synth" '[I, I, O] '[Ctx, Tm, Ty]
synth = judgment $ \rule ->
  [ rule "=>Var" $ do
      (ctx, x, ty) <- fresh3
      concl $ synth ctx (var x) ty
      prem  $ lookupCtx ctx x ty

  , rule "=>App" $ do
      (ctx, e1, e2, a, b) <- fresh5
      concl $ synth ctx (app e1 e2) b
      prem  $ synth ctx e1 (tarr a b)
      prem  $ check ctx e2 a
  ]
```

**Note: Judgments are Functions**

The type `Judgment "synth" '[I, I, O] '[Ctx, Tm, Ty]` is actually a **function type**:

```haskell
-- Judgment3 is a type alias for a function
type Judgment3 (name :: Symbol) (modes :: [Mode]) t1 t2 t3 =
  forall vs1 vs2 vs3.
    Term vs1 t1 -> Term vs2 t2 -> Term vs3 t3 -> JudgmentCall name modes ...

-- So `synth` is a function:
synth :: Term vs1 Ctx -> Term vs2 Tm -> Term vs3 Ty -> JudgmentCall "synth" ...
```

When you write `synth ctx e1 (tarr a b)`, you're calling this function, which returns a `JudgmentCall`. Then `prem` wraps that into the AST:

| Expression | Type |
|------------|------|
| `synth` | `Term -> Term -> Term -> JudgmentCall` |
| `synth ctx e1 ty` | `JudgmentCall "synth" ...` |
| `prem $ synth ctx e1 ty` | `RuleM ts s t ()` |

### DSL Primitives

```haskell
-- Fresh variables
fresh   :: (Repr a, Typeable a) => RuleM ts ... (Term '[n] a)
fresh2  :: ... => RuleM ts ... (Term '[n] a, Term '[n+1] b)
fresh3  :: ... => RuleM ts ... (Term '[n] a, Term '[n+1] b, Term '[n+2] c)

-- Conclusion and premises
concl :: JudgmentCall name modes ts -> RuleM ts ... ()
prem  :: JudgmentCall name modes ts -> RuleM ts ... ()

-- Constraints
(===) :: Term vs1 a -> Term vs2 a -> RuleM ts ... ()  -- equality
(=/=) :: Term vs1 a -> Term vs2 a -> RuleM ts ... ()  -- disequality

-- Negation as failure (inline rule)
neg :: RuleM ts' ... () -> RuleM ts ... ()
```

### Running Queries

```haskell
-- Typeset: extract rule structure, pretty-print
typeset :: Judgment name modes ts -> String

-- Eval: execute query, get results
eval :: Query a -> [a]
query :: Judgment name modes ts -> Args -> Query (Output modes ts)

-- Trace: execute + build derivation tree
trace :: Query a -> (a, DerivationTree)
```

### Example Usage

```haskell
main :: IO ()
main = do
  -- Typeset rules (no execution)
  putStrLn $ typeset synth

  -- Evaluate query
  let types = eval $ query synth emptyCtx (app (lam "x" (var "x")) unit)
  print types

  -- Get derivation tree
  let (ty, tree) = trace $ query synth emptyCtx term
  putStrLn $ prettyTree tree
```

---

## Core Types

### Term and Logic

```haskell
-- Term with type-level variable tracking
data Term (vs :: [Nat]) (a :: Type) = Term
  { termVars :: Set Int      -- Runtime var IDs (for scheduling)
  , termVal  :: Logic a      -- The value
  }

-- Logic value: variable or ground
data Logic a where
  Var    :: Int -> Logic a              -- Variable reference
  Ground :: Reified a -> Logic a        -- Constructor application
```

### Repr Class

```haskell
-- Existential wrapper for heterogeneous children
data Field where
  Field :: (Repr a, Typeable a) => Logic a -> Field

class Typeable a => Repr a where
  -- Reified representation with Logic children
  data Reified a :: Type

  -- Embed ground Haskell value
  project :: a -> Reified a

  -- Extract ground value (Nothing if contains variables)
  reify :: Reified a -> Maybe a

  -- Quote for pretty-printing: returns constructor name and children
  quote :: Reified a -> (String, [Field])
```

### User Syntax Definition

```haskell
-- 1. Define plain Haskell AST
data Ty = TInt | TVar TyNom | TArr Ty Ty

-- 2. Define Reified instance
data instance Reified Ty
  = RTInt
  | RTVar (Logic TyNom)
  | RTArr (Logic Ty) (Logic Ty)

-- 3. Implement Repr
instance Repr Ty where
  project TInt = RTInt
  project (TVar a) = RTVar (Ground (project a))
  project (TArr a b) = RTArr (Ground (project a)) (Ground (project b))

  reify RTInt = Just TInt
  reify (RTVar (Ground r)) = TVar <$> reify r
  reify (RTArr (Ground a) (Ground b)) = TArr <$> reify a <*> reify b
  reify _ = Nothing

  quote RTInt = ("Int", [])
  quote (RTVar a) = ("TVar", [Field a])
  quote (RTArr a b) = ("→", [Field a, Field b])

-- 4. Smart constructors
tint :: Term '[] Ty
tint = Term S.empty (Ground RTInt)

tarr :: Term vs1 Ty -> Term vs2 Ty -> Term (Union vs1 vs2) Ty
tarr = lift2 (\a b -> Ground (RTArr a b))
```

---

## Rule AST

### RuleF — Indexed Functor

```haskell
data RuleF (ts :: [Type]) (s :: St) (t :: St) (a :: Type) where

  -- Fresh variable
  FreshF :: (Repr a, Typeable a)
         => RuleF ts ('St n steps c) ('St (n + 1) steps c) (Term '[n] a)

  -- Conclusion (head of rule)
  ConclF :: JudgmentCall name modes vss ts
         -> RuleF ts ('St n steps 'False)
                     ('St n (Snoc steps ('ConcStep ...)) 'True) ()

  -- Premise
  PremF :: JudgmentCall name modes vss ts'
        -> RuleF ts ('St n steps c)
                    ('St n (Snoc steps ('PremStep ...)) c) ()

  -- Equality constraint
  EqF :: (Repr a, Typeable a)
      => Term vs1 a -> Term vs2 a
      -> RuleF ts ('St n steps c) ('St n (Snoc steps ...) c) ()

  -- Disequality constraint
  NEqF :: (Repr a, Typeable a)
       => Term vs1 a -> Term vs2 a
       -> RuleF ts ('St n steps c) ('St n (Snoc steps ...) c) ()

  -- Negation as failure
  NegF :: Rule ts'
       -> RuleF ts ('St n steps c) ('St n (Snoc steps ...) c) ()
```

### Rule and Judgment

```haskell
-- Rule monad
type RuleM ts s t a = IxFree (RuleF ts) s t a

-- A complete rule (existentially hides final state)
data Rule (ts :: [Type]) where
  Rule :: { ruleName :: String
          , ruleAST  :: RuleM ts ('St 0 '[] 'False) ('St n steps 'True) ()
          } -> Rule ts

-- A judgment is a collection of rules
data Judgment (name :: Symbol) (modes :: [Mode]) (ts :: [Type]) = Judgment
  { judgmentName  :: String
  , judgmentModes :: ModeList modes
  , judgmentRules :: [Rule ts]
  }

-- A judgment call (pure data)
data JudgmentCall (name :: Symbol) (modes :: [Mode]) (vss :: [[Nat]]) (ts :: [Type]) = JudgmentCall
  { jcJudgment :: Judgment name modes ts
  , jcArgs     :: TermList vss ts
  , jcReqVars  :: Set Int
  , jcProdVars :: Set Int
  }
```

### Compile-Time Mode Checking

The `CheckSchedule` constraint verifies at compile time:
1. All premises can be scheduled (inputs grounded)
2. All negations have grounded inputs
3. All conclusion outputs are produced

```haskell
ruleM :: forall name n steps ts.
         CheckSchedule name steps
      => String
      -> RuleM ts ('St 0 '[] 'False) ('St n steps 'True) ()
      -> Rule ts
```

---

## Interpreters

### Typeset Interpreter

Direct AST traversal, no execution:

```haskell
typeset :: Judgment name modes ts -> String
typeset j = unlines $ map typesetRule (judgmentRules j)

typesetRule :: Rule ts -> String
typesetRule (Rule name ast) = foldAST ast
  where
    -- Extract conclusion, premises, constraints
    -- Renumber variables (0,1,2 → x,y,z)
    -- Format as inference rule
```

### Eval Interpreter

Translates to miniKanren, executes:

```haskell
eval :: Query a -> [a]
eval q = map (extractResult q) (execute (translate q))

-- Pipeline:
-- 1. RuleF AST
-- 2. Reorder (optional)
-- 3. Translate to Goal
-- 4. Execute miniKanren
-- 5. Extract results from substitutions
```

### Trace Interpreter

Builds derivation tree from rule structure:

```haskell
trace :: Query a -> (a, DerivationTree)
trace q = (result, fillTree skeleton bindings)
  where
    skeleton = buildSkeleton (queryAST q)  -- From AST (before execution)
    bindings = execute (translate q)        -- From miniKanren
    result   = extractResult q bindings
```

The derivation tree reflects **rule structure**, not unification details:

```
         D1              D2
       ------          ------
    Γ ⊢ e1 : A→B     Γ ⊢ e2 : A
    ────────────────────────────  [⇒App]
          Γ ⊢ (e1 e2) : B
```

---

## MiniKanren Backend

Deeply embedded with typed GADTs.

### Goal AST

```haskell
-- Typed variable ID
newtype VarId a = VarId Int

-- Goal AST (deeply embedded)
data Goal where
  Fresh    :: (Repr a, Typeable a) => (VarId a -> Goal) -> Goal
  Unify    :: (Repr a, Typeable a) => Logic a -> Logic a -> Goal
  Disunify :: (Repr a, Typeable a) => Logic a -> Logic a -> Goal
  Conj     :: Goal -> Goal -> Goal
  Disj     :: Goal -> Goal -> Goal
  Neg      :: Goal -> Goal
  Success  :: Goal
  Failure  :: Goal
```

### Substitution

```haskell
data Subst = Subst (IntMap SomeBinding) Int

data SomeBinding where
  SomeBinding :: (Repr a, Typeable a) => Logic a -> SomeBinding

-- Type-safe lookup via Typeable
lookupVar :: (Repr a, Typeable a) => VarId a -> Subst -> Maybe (Logic a)
lookupVar (VarId i) (Subst m _) = do
  SomeBinding v <- IntMap.lookup i m
  cast v

-- Walk: follow variable chain
walk :: (Repr a, Typeable a) => Logic a -> Subst -> Logic a
walk (Var i) s = case lookupVar (VarId i) s of
  Just v  -> walk v s
  Nothing -> Var i
walk t _ = t
```

### Unification

```haskell
unify :: (Repr a, Typeable a) => Logic a -> Logic a -> Subst -> Maybe Subst
unify t1 t2 s = unify' (walk t1 s) (walk t2 s) s
  where
    unify' (Var i) t s
      | occursInLogic i t = Nothing  -- occurs check
      | otherwise = Just (extend i t s)
    unify' t (Var i) s
      | occursInLogic i t = Nothing
      | otherwise = Just (extend i t s)
    unify' (Ground r1) (Ground r2) s = unifyReified r1 r2 s

-- Occurs check via quote traversal
occursInLogic :: Repr a => Int -> Logic a -> Bool
occursInLogic i (Var j) = i == j
occursInLogic i (Ground r) = any (occursInField i) (snd (quote r))

occursInField :: Int -> Field -> Bool
occursInField i (Field t) = occursInLogic i t

-- Structural unification via quote
unifyReified :: (Repr a, Typeable a) => Reified a -> Reified a -> Subst -> Maybe Subst
unifyReified r1 r2 s
  | name1 /= name2 = Nothing
  | otherwise = unifyFields fields1 fields2 s
  where
    (name1, fields1) = quote r1
    (name2, fields2) = quote r2

unifyFields :: [Field] -> [Field] -> Subst -> Maybe Subst
unifyFields [] [] s = Just s
unifyFields (Field t1 : fs1) (Field t2 : fs2) s = do
  s' <- unifyField t1 t2 s
  unifyFields fs1 fs2 s'
unifyFields _ _ _ = Nothing

-- Unify two Fields (needs type equality check)
unifyField :: (Repr a, Typeable a, Repr b, Typeable b)
           => Logic a -> Logic b -> Subst -> Maybe Subst
unifyField t1 t2 s = case cast t2 of
  Just t2' -> unify t1 t2' s  -- Same type, unify
  Nothing  -> Nothing          -- Type mismatch

-- Display via quote traversal
displayLogic :: Repr a => Logic a -> String
displayLogic (Var i) = "?" ++ show i
displayLogic (Ground r) = displayReified r

displayReified :: Repr a => Reified a -> String
displayReified r = case quote r of
  (name, [])     -> name
  (name, fields) -> name ++ "(" ++ intercalate ", " (map displayField fields) ++ ")"

displayField :: Field -> String
displayField (Field t) = displayLogic t
```

### Execution

```haskell
exec :: Goal -> Subst -> [Subst]
exec Success s        = [s]
exec Failure _        = []
exec (Conj g1 g2) s   = concatMap (exec g2) (exec g1 s)
exec (Disj g1 g2) s   = interleave (exec g1 s) (exec g2 s)
exec (Fresh f) s      = let (v, s') = freshVar s in exec (f v) s'
exec (Unify t1 t2) s  = maybe [] pure (unify t1 t2 s)
exec (Disunify t1 t2) s = if canUnify t1 t2 s then [] else [s]
exec (Neg g) s        = if null (exec g s) then [s] else []

interleave :: [a] -> [a] -> [a]
interleave [] ys = ys
interleave (x:xs) ys = x : interleave ys xs
```

### Translation: RuleF → Goal

```haskell
translate :: Rule ts -> Goal
translate (Rule _ ast) = foldIxFree pure handle ast emptyEnv
  where
    handle :: RuleF ts s t x -> (x -> Env -> Goal) -> Env -> Goal
    handle FreshF k env =
      Fresh $ \v -> k (mkTerm v) (extendEnv v env)
    handle (EqF t1 t2) k env =
      Conj (Unify (resolve env t1) (resolve env t2)) (k () env)
    handle (NEqF t1 t2) k env =
      Conj (Disunify (resolve env t1) (resolve env t2)) (k () env)
    handle (NegF rule) k env =
      Conj (Neg (translate rule)) (k () env)
    handle (PremF call) k env =
      Conj (translatePrem call env) (k () env)
    handle (ConclF call) k env =
      Conj (translateConcl call env) (k () env)
```

---

## Module Structure

```
typedredex-pure/
├── src/TypedRedex/
│   │
│   ├── DSL.hs                 -- Re-exports user API
│   │
│   ├── DSL/
│   │   ├── Syntax.hs          -- judgment, fresh, concl, prem, ===, =/=, neg
│   │   └── Term.hs            -- Term, lift1, lift2, ground
│   │
│   ├── Core/
│   │   ├── Term.hs            -- Term, Logic, Repr class
│   │   ├── RuleF.hs           -- RuleF, RuleM
│   │   ├── Judgment.hs        -- Judgment, Rule, JudgmentCall
│   │   ├── IxFree.hs          -- Indexed free monad
│   │   └── Schedule.hs        -- Compile-time mode checking
│   │
│   ├── Interp/
│   │   ├── Typeset.hs         -- Typeset interpreter
│   │   ├── Eval.hs            -- Eval interpreter
│   │   ├── Trace.hs           -- Trace interpreter
│   │   └── Reorder.hs         -- AST reordering pass
│   │
│   └── Backend/
│       ├── Goal.hs            -- Goal AST
│       ├── Subst.hs           -- Substitution
│       ├── Unify.hs           -- Unification
│       └── Exec.hs            -- Execution
│
└── examples/
    └── poly/
        ├── Syntax.hs          -- Ty, Tm, Env definitions + Repr instances
        └── Rules.hs           -- Judgments: isEvar, ssub, synth, check
```

---

## Differences from Previous Approach

| Aspect | Previous | New |
|--------|----------|-----|
| **AST parameterization** | `RuleF rel ts s t a` | `RuleF ts s t a` (no `rel`) |
| **Term type** | `T vs a rel` with `Logic a (RVar rel)` | `Term vs a` with `Logic a` |
| **Variables** | `RVar rel a` (monad-specific) | `Int` with phantom type |
| **Type class** | `LogicRepr a` with `Reified a var` | `Repr a` with `Reified a` (no `var`) |
| **Judgment type** | `Judgment rel name modes ts` | `Judgment name modes ts` |
| **User constraints** | `PolyRel rel` | None |
| **miniKanren** | Shallow embedded (`Redex` class) | Deeply embedded (`Goal` GADT) |
| **Typesetting** | Needed `DummyRel` | Direct AST traversal |
| **Multi-backend** | Rebuild AST for each | Same AST, different interpreters |

### Why the Change?

1. **`rel` was leaking**: Users saw miniKanren internals (`RVar rel`) in their types
2. **AST wasn't pure data**: Contained `rel ()` thunks, couldn't serialize or inspect
3. **Switching backends required rebuilding**: Rules built with `Rel` couldn't use `TracingRel`
4. **Typesetting was awkward**: Needed dummy monad to extract structure
5. **miniKanren is implementation detail**: Users write Redex rules, not miniKanren goals
