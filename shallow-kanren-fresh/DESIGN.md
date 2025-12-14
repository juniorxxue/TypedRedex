# Fresh-Aware shallow-kanren: Design and Implementation

## Motivation

The original shallow-kanren library uses **pure functions** for the `LogicType` typeclass, which works well for terms using de Bruijn indices but is **incompatible with unbound-generics**, a popular Haskell library for handling variable binding with automatic α-equivalence.

### Why unbound-generics?

unbound-generics provides:
- **Named variables** instead of de Bruijn indices (more readable)
- **Automatic α-equivalence** via the `Alpha` typeclass
- **Safe binding** via the `Bind` type constructor
- **Capture-avoiding substitution** automatically handled

### The Incompatibility Problem

unbound-generics requires the `Fresh` monad for its core operations:

```haskell
-- From unbound-generics:
unbind :: Fresh m => Bind n t -> m (n, t)
bind :: Fresh m => n -> t -> m (Bind n t)
aeq :: Fresh m => Alpha t => t -> t -> m Bool
```

But the original shallow-kanren `LogicType` has **pure** methods:

```haskell
-- Original (pure):
class LogicType a where
  project :: a -> Reified a var                    -- No monad!
  reify :: Reified a var -> Maybe a                -- No monad!
  unifyVal :: ... -> Reified a var -> Reified a var -> rel ()
  derefVal :: ... -> Reified a var -> rel a
```

**Result**: Cannot use `unbind` inside `project` because there's no `Fresh` monad available.

### Design Goal

Modify shallow-kanren's architecture to support the `Fresh` monad, enabling:
1. Direct use of unbound-generics `Bind` types in term representations
2. Use of `unbind` in `project` to extract names and bodies
3. Use of `bind` in `reify` to construct bindings
4. Potential use of `aeq` for α-equivalence checking in unification

---

## Overview of Changes

The modified architecture makes **all core operations monadic** with a `Fresh` constraint:

```haskell
-- Modified (monadic with Fresh):
class LogicType a where
  project :: (Monad m, Fresh m) => a -> m (Reified a var)
  reify :: (Monad m, Fresh m) => Reified a var -> m (Maybe a)
  unifyVal :: (Alternative rel, Fresh rel) => ...
  derefVal :: (Alternative m, Monad m, Fresh m) => ...
```

The key insight: **Make the relation monad (`rel`) also implement `Fresh`**, so all LogicType operations can use Fresh actions.

---

## Detailed Changes

### 1. Core Type Definitions (`Shallow.Core.Internal.Logic`)

#### Original:
```haskell
class LogicType a where
  data Reified a (var :: Type -> Type) :: Type
  project :: a -> Reified a var
  reify :: Reified a var -> Maybe a
  unifyVal :: (Alternative rel) =>
    (forall t. LogicType t => Logic t var -> Logic t var -> rel ())
    -> Reified a var -> Reified a var -> rel ()
  derefVal :: (Alternative m) =>
    (forall t. LogicType t => Logic t var -> m t)
    -> Reified a var -> m a
```

#### Modified:
```haskell
import Unbound.Generics.LocallyNameless (Fresh)

class LogicType a where
  data Reified a (var :: Type -> Type) :: Type

  -- Now monadic with Fresh constraint
  project :: (Monad m, Fresh m) => a -> m (Reified a var)
  reify :: (Monad m, Fresh m) => Reified a var -> m (Maybe a)

  -- unifyVal now requires Fresh on the relation monad
  unifyVal :: (Alternative rel, Fresh rel) =>
    (forall t. LogicType t => Logic t var -> Logic t var -> rel ())
    -> Reified a var -> Reified a var -> rel ()

  -- derefVal also requires Fresh
  derefVal :: (Alternative m, Monad m, Fresh m) =>
    (forall t. LogicType t => Logic t var -> m t)
    -> Reified a var -> m a
```

**Impact**: All `LogicType` instances must now provide monadic implementations.

---

### 2. Kanren Typeclass (`Shallow.Core.Internal.Kanren`)

#### Original:
```haskell
class (Alternative rel, Functor (KVar rel)) => Kanren rel where
  data KVar rel :: Type -> Type
  fresh_ :: (LogicType t) => FreshType rel t -> (Var t (KVar rel) -> rel a) -> rel a
  unify :: (LogicType a) => Logic a (KVar rel) -> Logic a (KVar rel) -> rel ()
  call_ :: CallType -> Relation rel -> rel ()
  displayVar :: KVar rel t -> String
```

#### Modified:
```haskell
import Unbound.Generics.LocallyNameless (Fresh)

class (Alternative rel, Fresh rel, Functor (KVar rel)) => Kanren rel where
  --                     ^^^^^^^^ Added Fresh constraint!
  data KVar rel :: Type -> Type
  fresh_ :: (LogicType t) => FreshType rel t -> (Var t (KVar rel) -> rel a) -> rel a
  unify :: (LogicType a) => Logic a (KVar rel) -> Logic a (KVar rel) -> rel ()
  call_ :: CallType -> Relation rel -> rel ()
  displayVar :: KVar rel t -> String
```

**Key Change**: Added `Fresh rel` constraint. Now any monad that implements `Kanren` must also implement `Fresh`.

---

### 3. SubstKanren Interpreter (`Shallow.Interpreters.SubstKanrenFresh`)

#### Original:
```haskell
newtype SubstKanren s a = SubstKanren (StateT (Subst s) Stream a)
  deriving (Functor, Applicative, Alternative, Monad)
```

#### Modified:
```haskell
import Unbound.Generics.LocallyNameless (FreshMT, Fresh, runFreshMT)

-- Stack FreshMT on top of the existing monad stack
newtype SubstKanrenFresh s a = SubstKanrenFresh
  { unSubstKanrenFresh :: FreshMT (StateT (Subst s) Stream) a
  }
  deriving (Functor, Applicative, Alternative, Monad, Fresh)
  --                                                     ^^^^^ Derived automatically!

-- Kanren instance now satisfies Fresh constraint
instance Kanren (SubstKanrenFresh s) where
  newtype instance (KVar (SubstKanrenFresh s)) t = SVar VarRepr deriving (Functor, Show)

  fresh_ FreshVar   = (makeVar Nothing >>=)
  fresh_ (ArgVar x) = (makeVar (Just x) >>=)

  unify = flatteningUnify unif
    where
      unif v y
        | occursCheck v y = empty
        | otherwise = do
            x <- readVar v
            maybe (modify $ updateSubst v (Just y)) (unify y) x

  -- Handle FreshMT in call_
  call_ Opaque (Relation _ (SubstKanrenFresh r)) =
    SubstKanrenFresh $ lift $ mapStateT Immature $ runFreshMT r
  call_ Transparent (Relation _ r) = r

  displayVar (SVar v) = "x" ++ show v

-- Run function extracts Fresh state
runSubstKanrenFresh :: (forall s. SubstKanrenFresh s t) -> Stream t
runSubstKanrenFresh (SubstKanrenFresh r) = evalStateT (runFreshMT r) emptySubst
```

**Key Changes**:
1. Wrap the existing `StateT (Subst s) Stream` with `FreshMT`
2. Derive `Fresh` instance automatically
3. Use `runFreshMT` to run the Fresh monad when needed
4. Adjust `call_` to handle the extra monad layer

**Monad Stack**: `FreshMT (StateT (Subst s) Stream)`
- Inner: `StateT (Subst s) Stream` - substitution + backtracking
- Outer: `FreshMT` - fresh name generation

---

### 4. Utility Functions (`Shallow.Utils.Kanren`)

Most utility functions remain the same, but some need to handle monadic LogicType:

#### Modified:
```haskell
-- eval now works with monadic derefVal
eval :: (KanrenEval rel, LogicType a) => L a rel -> rel a
eval (Free v) = derefVar v
eval (Ground x) = derefVal eval x  -- derefVal is now monadic

-- flatteningUnify works with monadic unifyVal
flatteningUnify :: (Alternative rel, Kanren rel, LogicType a) =>
  (forall a'. (LogicType a') => Var' a' rel -> L a' rel -> rel ()) ->
  L a rel -> L a rel -> rel ()
flatteningUnify unifyVar (Free a) b = unifyVar a b
flatteningUnify unifyVar a (Free b) = unifyVar b a
flatteningUnify unifyVar (Ground a) (Ground b) = unifyVal (flatteningUnify unifyVar) a b
```

---

## Using unbound-generics with the Modified Library

### Example: Lambda Calculus Terms

```haskell
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}

import Unbound.Generics.LocallyNameless

type TmName = Name Tm

data Tm
  = Var TmName                 -- Named variable
  | Lam (Bind TmName Tm)       -- λx.e with binding
  | App Tm Tm
  deriving (Show, Generic, Typeable)

-- Required instances for unbound-generics
instance Alpha Tm
instance Subst Tm Tm where
  isvar (Var x) = Just (SubstName x)
  isvar _ = Nothing
```

### LogicType Instance with Fresh

```haskell
instance LogicType Tm where
  data Reified Tm var
    = VarR TmName
    | LamR TmName (Logic Tm var)   -- Unbind stores name + body separately
    | AppR (Logic Tm var) (Logic Tm var)

  -- MONADIC project - can use unbind!
  project (Var x) = pure $ VarR x
  project (Lam b) = do
    (x, body) <- unbind b           -- unbind :: Fresh m => Bind n t -> m (n, t)
    bodyR <- project body            -- Recursive project
    pure $ LamR x (Ground bodyR)
  project (App f a) = do
    fR <- project f
    aR <- project a
    pure $ AppR (Ground fR) (Ground aR)

  -- MONADIC reify - can use bind!
  reify (VarR x) = pure $ Just (Var x)
  reify (LamR x (Ground body)) = do
    bodyM <- reify body
    pure $ Lam . bind x <$> bodyM   -- bind :: Fresh m => n -> t -> m (Bind n t)
  reify (AppR (Ground f) (Ground a)) = do
    fM <- reify f
    aM <- reify a
    pure $ App <$> fM <*> aM
  reify _ = pure Nothing

  -- Unification with name matching
  unifyVal unif (VarR x) (VarR y)
    | x == y = pure ()
    | otherwise = empty
  unifyVal unif (LamR x body) (LamR y body')
    | x == y = unif body body'  -- Names must match (could use aeq for α-equiv)
    | otherwise = empty
  unifyVal unif (AppR f a) (AppR f' a') =
    unif f f' *> unif a a'
  unifyVal _ _ _ = empty

  quote (VarR x) = (name2String x, [])
  quote (LamR x body) = ("Lam_" ++ name2String x, [])
  quote (AppR f a) = ("App", [])

  derefVal deref (VarR x) = pure (Var x)
  derefVal deref (LamR x body) = do
    body' <- deref body
    pure $ Lam (bind x body')
  derefVal deref (AppR f a) =
    App <$> deref f <*> deref a
```

### Running Queries

```haskell
import Shallow.Interpreters.SubstKanrenFresh (runSubstKanrenFresh)

-- Example query
example :: IO ()
example = do
  let id_term = Lam (bind (s2n "x") (Var (s2n "x")))

  let query = runSubstKanrenFresh $ fresh $ \t -> do
        tR <- project id_term
        t <=> Ground tR
        eval t

  print $ takeS 1 query
  -- Output: [Lam (<x> Var 0@0)]
```

---

## Examples Included

### 1. `examples-fresh/fresh-lambda/Main.hs`
Basic lambda calculus demonstrating:
- Use of `Bind` from unbound-generics
- `unbind` in `project`
- `bind` in `reify`
- Unification with named variables

### 2. `examples-fresh/stlc-bidir/Main.hs`
Simplified bidirectional typing demonstrating:
- STLC with type annotations
- Type synthesis relations
- Fresh monad throughout LogicType operations

---

## Performance Considerations

### Overhead

The modified library adds `FreshMT` to the monad stack, which introduces:
1. **Fresh name generation state** (maintained by unbound-generics)
2. **One additional monad layer** in the stack

### When to Use This Version

**Use Fresh-aware shallow-kanren when**:
- Working with lambda calculi or languages with binding
- Need α-equivalence automatically handled
- Prefer named variables over de Bruijn indices
- Using unbound-generics elsewhere in your codebase

**Use original shallow-kanren when**:
- No variable binding in your domain
- Performance is critical and you can use de Bruijn indices
- Don't need unbound-generics features

---

## Migration Guide

### From Original to Fresh-Aware

1. **Update LogicType instances**:
   ```haskell
   -- Before:
   project (Lam body) = LamR (Ground $ project body)

   -- After:
   project (Lam body) = do
     bodyR <- project body
     pure $ LamR (Ground bodyR)
   ```

2. **Use Fresh-aware interpreter**:
   ```haskell
   -- Before:
   import Shallow.Interpreters.SubstKanren (runSubstKanren)

   -- After:
   import Shallow.Interpreters.SubstKanrenFresh (runSubstKanrenFresh)
   ```

3. **Add Fresh constraints where needed**:
   ```haskell
   -- Before:
   myRelation :: (Kanren rel) => L Tm rel -> Relation rel

   -- After (no change needed - Fresh is already in Kanren):
   myRelation :: (Kanren rel) => L Tm rel -> Relation rel
   ```

4. **Handle monadic project in queries**:
   ```haskell
   -- Before:
   runSubstKanren $ do
     let termR = project myTerm
     ...

   -- After:
   runSubstKanrenFresh $ do
     termR <- project myTerm  -- Now monadic!
     ...
   ```

---

## Summary

The Fresh-aware shallow-kanren modifies the original library to support the `Fresh` monad by:

1. **Making LogicType monadic** - All methods now work in a monad with Fresh constraint
2. **Adding Fresh to Kanren** - The Kanren typeclass requires Fresh on the relation monad
3. **Stacking FreshMT** - SubstKanren wraps its monad stack with FreshMT from unbound-generics
4. **Enabling unbound-generics** - Can now use Bind, unbind, bind, and aeq directly

This design enables clean integration with unbound-generics while maintaining the relational programming model of miniKanren. The trade-off is added monadic overhead, but in return you get automatic α-equivalence, named variables, and safe binding operations.
