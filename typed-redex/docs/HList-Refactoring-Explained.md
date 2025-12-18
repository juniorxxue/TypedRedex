# Type-Level Lists Refactoring: From Applied2/3/4/5 to Applied rel '[...]

This document explains the refactoring that unified multiple arity-specific types into a single type parameterized by a type-level list.

## The Problem

Before the refactoring, we had separate types for each arity:

```haskell
data Applied2 rel a b = Applied2 { app2Args :: (LTerm a rel, LTerm b rel), app2Goal :: rel () }
data Applied3 rel a b c = Applied3 { app3Args :: (LTerm a rel, LTerm b rel, LTerm c rel), app3Goal :: rel () }
data Applied4 rel a b c d = Applied4 { ... }
data Applied5 rel a b c d e = Applied5 { ... }
```

This led to:
- **Code duplication**: 5 nearly identical type definitions
- **Verbose user code**: `Applied4 rel Nat Ty Nat Ty` instead of something simpler
- **Separate functions**: `judgment2`, `judgment3`, `judgment4`, `rule2`, `rule3`, etc.
- **Hard to extend**: Adding 6-ary relations would require yet another copy

## The Solution: Type-Level Lists

After refactoring, we have one unified type:

```haskell
data Applied rel (ts :: [Type]) = Applied
  { appArgs :: LTermList rel ts
  , appGoal :: rel ()
  }
```

User code becomes:
```haskell
-- Before
substTyVar :: Redex rel => LTerm Nat rel -> LTerm Ty rel -> LTerm Nat rel -> LTerm Ty rel -> Applied4 rel Nat Ty Nat Ty

-- After
substTyVar :: Redex rel => Judge rel '[Nat, Ty, Nat, Ty]
```

## Key Haskell Concepts

### 1. DataKinds Extension

Normally, `[Int, Bool]` is a value-level list. With `DataKinds`, types can be "promoted" to the kind level:

```haskell
{-# LANGUAGE DataKinds #-}

-- '[Int, Bool] is a TYPE-LEVEL list (note the tick mark ')
-- Its kind is [Type] (a list of types)
type MyTypes = '[Int, Bool, String]
```

The tick mark `'` distinguishes type-level lists from value-level ones.

### 2. GADTs (Generalized Algebraic Data Types)

GADTs let constructors specify exact return types:

```haskell
{-# LANGUAGE GADTs #-}

-- A heterogeneous list indexed by a type-level list
data LTermList rel (ts :: [Type]) where
  TNil  :: LTermList rel '[]                                      -- Empty list has type '[]
  (:>)  :: LTerm t rel -> LTermList rel ts -> LTermList rel (t ': ts)  -- Cons adds t to front
```

This creates a **heterogeneous list** - each element can have a different type, and the type-level list tracks what types are present:

```haskell
example :: LTermList rel '[Nat, Ty, Nat]
example = natTerm :> tyTerm :> natTerm2 :> TNil
--        ^Nat      ^Ty       ^Nat        ^'[]
```

### 3. Type Families

Type families are type-level functions. We use them to compute curried function types:

```haskell
{-# LANGUAGE TypeFamilies #-}

-- Computes: '[A, B, C] -> (LTerm A rel -> LTerm B rel -> LTerm C rel -> r)
type family CurriedR rel (ts :: [Type]) (r :: Type) where
  CurriedR rel '[]       r = r                              -- Base case: just return r
  CurriedR rel (t ': ts) r = LTerm t rel -> CurriedR rel ts r  -- Recursive: add an argument
```

Example expansion:
```
CurriedR rel '[Nat, Ty] (Applied rel '[Nat, Ty])
= LTerm Nat rel -> CurriedR rel '[Ty] (Applied rel '[Nat, Ty])
= LTerm Nat rel -> LTerm Ty rel -> CurriedR rel '[] (Applied rel '[Nat, Ty])
= LTerm Nat rel -> LTerm Ty rel -> Applied rel '[Nat, Ty]
```

### 4. Type Classes for Type-Level Recursion

Since type families just compute types, we need type classes to compute values:

```haskell
class BuildLTermList rel ts where
  buildLTermList :: (LTermList rel ts -> r) -> CurriedR rel ts r

-- Base case: empty list
instance BuildLTermList rel '[] where
  buildLTermList f = f TNil

-- Recursive case: consume one argument, recurse
instance (LogicType t, BuildLTermList rel ts) => BuildLTermList rel (t ': ts) where
  buildLTermList f x = buildLTermList (\rest -> f (x :> rest))
```

This uses **continuation-passing style**: instead of building the list directly, we pass a continuation `f` that will receive the final list.

## How `judgment` Works

The unified `judgment` function:

```haskell
judgment :: (BuildLTermList rel ts, Redex rel, ArgumentList rel ts, UnifyList rel ts)
         => String -> [Rule rel ts] -> CurriedR rel ts (Applied rel ts)
judgment name rules = buildLTermList $ \args ->
  Applied args $ argumentList args $ \args' ->
    let terms = captureTerms args
    in let ?concl = \pat -> unifyList args' pat
    in asum [call $ Relation (ruleName r) terms (ruleBody r) | r <- rules]
```

Step by step:
1. `buildLTermList` collects curried arguments into an `LTermList`
2. `argumentList` binds each argument to a fresh logic variable
3. `captureTerms` wraps terms for derivation tracking
4. `?concl` is an implicit parameter that rules use to declare conclusions
5. `asum` tries each rule as an alternative

## The Judge Type Alias

```haskell
type Judge rel ts = CurriedR rel ts (Applied rel ts)
```

This expands the curried function type, so:

```haskell
Judge rel '[Ctx, Tm, Ty] = LTerm Ctx rel -> LTerm Tm rel -> LTerm Ty rel -> Applied rel '[Ctx, Tm, Ty]
```

**Important**: We define `Judge` using `CurriedR` (not `Curried`) because that's exactly what `judgment` returns. Type families don't unify with equivalent type families, so the definitions must match exactly.

## Summary of Changes

| Before | After |
|--------|-------|
| `Applied2 rel A B` | `Applied rel '[A, B]` |
| `Applied3 rel A B C` | `Applied rel '[A, B, C]` |
| `app3Goal` | `appGoal` |
| `judgment3 "name" [...]` | `judgment "name" [...]` |
| `rule3 "name" $ ...` | `rule "name" $ ...` |
| Long explicit type sig | `Judge rel '[A, B, C]` |

## Extensions Required

```haskell
{-# LANGUAGE DataKinds #-}        -- Type-level lists like '[A, B, C]
{-# LANGUAGE GADTs #-}            -- LTermList GADT
{-# LANGUAGE TypeFamilies #-}     -- CurriedR type family
{-# LANGUAGE TypeOperators #-}    -- (':) type operator for lists
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}  -- Recursive type class instances
```

## Further Reading

- [GHC User Guide: DataKinds](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/data_kinds.html)
- [GHC User Guide: Type Families](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/type_families.html)
- [GHC User Guide: GADTs](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/gadt.html)
- [Heterogeneous Lists (HList paper)](http://okmij.org/ftp/Haskell/HList-ext.pdf)
