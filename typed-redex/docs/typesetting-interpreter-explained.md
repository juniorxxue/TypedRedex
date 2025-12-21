# Typesetting Interpreter: How Rule Extraction Works

This document explains the logic in `TypedRedex.Interp.Typesetting`, which extracts human-readable inference rules from relation definitions.

## Overview

The typesetting interpreter transforms executable relation definitions into printable inference rules. Given a judgment like:

```haskell
synth :: Judge rel '[Ctx, Tm, Ty]
synth = judgment "synth" [synthVar, synthUnit, ...]
```

It produces output like:

```
  Γ(x) = A
  ──────────────── [⇒Var]
  Γ ⊢ x ⇒ A
```

## Architecture: Direct Rule Building

The key insight is that `concl` and `prem` emit **structural markers** that the typesetting interpreter uses to build `ExtractedRule` directly—no intermediate AST needed.

### Data Structures

```haskell
-- The only output type we need
data ExtractedRule = ExtractedRule
  { erName     :: String                  -- Rule name (e.g., "typeof-lam")
  , erPatterns :: [String]                -- Conclusion patterns
  , erPremises :: [(String, [String])]    -- Premises as (judgment-name, args)
  }

-- State accumulated during tracing
data RuleBuilder = RuleBuilder
  { rbName        :: String
  , rbInConclusion :: Bool    -- After markConclusion?
  , rbPatterns    :: [String] -- Conclusion patterns (reverse order)
  , rbPremises    :: [(String, [String])] -- Premises (reverse order)
  }
```

### Marker Methods in Redex Typeclass

```haskell
class Redex rel where
  ...
  -- Structural markers (no-op for execution interpreters)
  markConclusion :: rel ()
  markConclusion = pure ()

  markPremise :: String -> [CapturedTerm rel] -> rel ()
  markPremise _ _ = pure ()
```

### How Markers Flow

In `DSL/Define.hs`:

```haskell
-- concl emits a marker before unifying
instance Redex rel => Conclude (Applied rel ts) rel where
  concl (Applied args _ _) = do
    markConclusion              -- Emit marker
    ?concl args                 -- Then do unifications

-- prem emits a marker before running the goal
instance Redex rel => Premise (Applied rel ts) rel where
  prem (Applied args g name) = do
    markPremise name (captureTerms args)  -- Emit marker with judgment name
    g                                      -- Then run the goal
```

## TypesettingRedex Implementation

The interpreter traces rule execution and builds `ExtractedRule` directly:

```haskell
instance Redex TypesettingRedex where
  -- markConclusion: switch to "recording conclusion patterns" mode
  markConclusion = modify $ \s ->
    s { tsBuilder = (tsBuilder s) { rbInConclusion = True } }

  -- unify: if in conclusion mode, record the pattern
  unify x y = do
    inConcl <- gets (rbInConclusion . tsBuilder)
    when inConcl $ do
      fmt <- gets tsFormatter
      let rhs = prettyLFmt fmt y
      modify $ \s -> s { tsBuilder = ... { rbPatterns = rhs : rbPatterns ... } }

  -- markPremise: record the premise call with its arguments
  markPremise name args = do
    argStrs <- mapM prettyCaptured args
    modify $ \s -> s { tsBuilder = ... { rbPremises = (name, argStrs) : ... } }

  -- call_: depth 0→1 enters a rule, depth >0 stops expansion
  call_ _ rel = do
    depth <- gets tsDepth
    if depth == 0
      then do
        modify $ \s -> s { tsBuilder = ... { rbName = relName rel }, tsDepth = 1 }
        relBody rel
        modify $ \s -> s { tsDepth = 0 }
      else pure ()  -- Don't expand nested calls
```

### Branching (Alternative)

When rules have disjunctions (`<|>`), each branch produces a separate rule:

```haskell
instance Alternative TypesettingRedex where
  a <|> b = do
    s0 <- get
    -- Run branch a, collect rules
    put $ s0 { tsBuilder = emptyBuilder, tsRules = [] }
    _ <- a
    rulesA <- collectRules
    -- Run branch b, collect rules
    put $ s0 { tsBuilder = emptyBuilder, tsRules = [] }
    _ <- b
    rulesB <- collectRules
    -- Combine all rules
    put $ s0 { tsRules = tsRules s0 ++ rulesA ++ rulesB }
```

## Data Flow

```
User code                    TypesettingRedex monad             Output
─────────────────────────────────────────────────────────────────────────
rule "β" $ ... -> do
  concl $ ...              ─▶  markConclusion + unify (record patterns)
  prem $ value ...         ─▶  markPremise "value" [...] (record premise)
  prem $ subst0 ...        ─▶  markPremise "subst0" [...] (record premise)
                                           │
                                           ▼
                             finishRule ─▶ ExtractedRule{name, patterns, premises}
                                           │
                                           ▼
                             formatRule ─▶ ASCII inference rule
```

## Variable Renumbering

Variables are initially recorded with internal markers:

```
«E:3» = App(«E:5», «E:7»)
```

The `renumberVars` function parses these markers and assigns readable names per-tag:

```haskell
parseVarMarkers :: String -> [(String, Int)]  -- Find all «TAG:ID» markers
buildRenumberMap :: [(String, Int)] -> [((String, Int), Int)]  -- Assign 0,1,2... per tag
varNameByTag :: String -> Int -> String  -- "E" + 0 → "e", "T" + 1 → "B", etc.
```

Output after renumbering:
```
e = App(e₁, e₂)
```

## Why This Design Works

**Before** (complex Goal AST + extraction phase):
- Built a generic `Goal` AST during tracing
- Needed `extractRule` to walk the AST and recover structure
- Had to infer which `GUnify` nodes were conclusions vs. internal
- Required depth tracking and phase state machine

**After** (direct rule building):
- `concl` and `prem` emit structural markers
- TypesettingRedex builds `ExtractedRule` directly during tracing
- No intermediate AST, no extraction phase
- ~370 lines instead of ~630 lines

## Files Involved

| File | Role |
|------|------|
| `Core/Internal/Redex.hs` | Defines `markConclusion`, `markPremise` (default no-op) |
| `DSL/Define.hs` | `concl`/`prem` emit markers; `Applied` stores judgment name |
| `Interp/Typesetting.hs` | `TypesettingRedex` interpreter builds `ExtractedRule` directly |
