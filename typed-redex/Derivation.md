# Derivation System Design

## ✅ Implementation Status (Completed)

The recommended approach (Proposal 1 + 2) has been implemented:

1. **CapturedTerm existential** (`Core/Internal/Redex.hs`): Logic terms are wrapped in `CapturedTerm` instead of being converted to strings immediately.

2. **Deferred resolution** (`TracingRedex.hs`): Terms are resolved to strings at `popFrame` time, AFTER unification completes, ensuring derivations show actual values.

3. **JudgmentFormatter typeclass** (`TracingRedex.hs`): Users define custom formatting in their examples. The library only provides:
   - `JudgmentFormatter` typeclass
   - `defaultFormatConclusion`: Simple application-style `name(arg1, arg2, ...)`
   - `DefaultFormatter`: Uses application-style (no domain-specific patterns)

### Key Changes

```haskell
-- Before: captured strings immediately (broken)
data Relation rel = Relation { relName :: String, relArgs :: [String], ... }

-- After: capture terms, resolve later (fixed)
data CapturedTerm rel where
  CapturedTerm :: LogicType a => Logic a (RVar rel) -> CapturedTerm rel

data Relation rel = Relation { relName :: String, relTerms :: [CapturedTerm rel], ... }
```

### User-Defined Formatting (in examples, not library)

```haskell
-- In examples/system-f/Main.hs
data SystemFFormatter = SystemFFormatter

instance JudgmentFormatter SystemFFormatter where
  formatConclusion _ "typeof" [ctx, e, ty] = ctx ++ " ⊢ " ++ e ++ " : " ++ ty
  formatConclusion _ "natLt" [n, m] = n ++ " < " ++ m
  formatConclusion _ name args = defaultFormatConclusion name args

prettyDerivation = prettyDerivationWith SystemFFormatter
```

### Results

Derivations now show actual values:
- Before: `x0 < x1` (unresolved variables)
- After: `S(Z) < S(S(S(Z)))` (resolved values)

---

## Original Limitations (Now Fixed)

1. **Variables not resolved in derivations**: TracingRedex derivation trees show unresolved variable names (`x0`, `x1`, etc.) instead of actual values because arguments are pretty-printed BEFORE unification completes.

2. **Hardcoded judgment formatting**: The `formatConclusion` function in `TracingRedex.hs` contains hardcoded patterns like:
   ```haskell
   formatConclusion "typeof" [ctx, e, ty] = ctx ++ " ⊢ " ++ e ++ " : " ++ ty
   ```
   This should be user-definable in examples, not built into the library.

3. **Variable numbering inconsistencies**: Fresh variables created during rule execution get arbitrary indices that don't match the logical structure of the rule.

## Root Cause Analysis

The problem stems from the architecture in `Utils/Define.hs`:

```haskell
judgment2 _ rules x y = Applied2 (x, y) $ argument2 x y $ \x' y' ->
  let args = [prettyLogic x', prettyLogic y']  -- Captured HERE, before unification!
  in let ?concl = ...
  in asum [call $ Relation (rule2Name r) args (rule2Body r) | r <- rules]
```

When `judgment2` is called:
1. `prettyLogic x'` captures the current representation of `x'` (often just `"x0"`)
2. This string is stored in `Relation { relArgs = [...] }`
3. TracingRedex's `call_` pushes this string to the derivation frame
4. Unification happens AFTER the frame is created
5. When we pop the frame, the args still contain `"x0"` instead of the resolved value

---

## Proposal 1: Deferred Pretty-Printing with Captured Terms

### Idea

Store the actual logic terms (wrapped in an existential) instead of pre-computed strings. Apply the final substitution when rendering the derivation tree.

### Design

```haskell
-- A captured term that can be pretty-printed later
data CapturedTerm rel where
  Captured :: LogicType a => L a rel -> CapturedTerm rel

-- Modified Relation type
data Relation rel = Relation
  { relName  :: String
  , relTerms :: [CapturedTerm rel]  -- Terms instead of strings
  , relBody  :: rel ()
  }

-- Modified DerivFrame
data DerivFrame rel = DerivFrame
  { frameName     :: String
  , frameTerms    :: [CapturedTerm rel]  -- Captured terms
  , frameChildren :: [Derivation rel]
  }

-- At render time, resolve terms using final substitution
renderDeriv :: Subst rel -> Derivation rel -> String
renderDeriv subst (Deriv name terms children) =
  let args = map (resolveTerm subst) terms
  in formatConclusion name args
```

### Changes Required

1. **Relation type**: Store `[CapturedTerm rel]` instead of `[String]`
2. **TracingState**: Keep terms in frames, carry substitution through
3. **runTracingRedex**: Apply final substitution to all derivation nodes before returning
4. **Existential wrapper**: `CapturedTerm` hides the type but preserves the term

### Pros
- Derivations show actual resolved values
- Clean semantics: derivation structure is independent of rendering
- No user-facing API changes for defining relations

### Cons
- Existential types add complexity
- Need to thread substitution through entire derivation tree at render time
- May need to keep variables alive longer (GC implications)

### User Formatting

Add a separate formatting typeclass:
```haskell
class JudgmentFormatter where
  formatJudgment :: String -> [String] -> String

-- Users provide instance in their code
instance JudgmentFormatter where
  formatJudgment "typeof" [ctx, e, ty] = ctx ++ " ⊢ " ++ e ++ " : " ++ ty
  formatJudgment "step" [a, b] = a ++ " ⟶ " ++ b
  formatJudgment name args = name ++ "(" ++ intercalate ", " args ++ ")"
```

---

## Proposal 2: User-Provided Formatter via Typeclass

### Idea

Let users define how their judgments should be formatted by implementing a typeclass. The library provides a default implementation, but users can override it.

### Design

```haskell
-- User implements this for their domain
class JudgmentStyle where
  -- Format a conclusion given judgment name and resolved argument strings
  formatConclusion :: String -> [String] -> String
  formatConclusion name args = defaultFormat name args

  -- Format the horizontal line
  formatLine :: Int -> String -> String
  formatLine width ruleName = replicate width '─' ++ " [" ++ ruleName ++ "]"

-- Library provides default
defaultFormat :: String -> [String] -> String
defaultFormat name [] = name
defaultFormat name args = name ++ "(" ++ intercalate ", " args ++ ")"

-- TracingRedex parameterized by formatter
runTracingRedexWith :: JudgmentStyle fmt
                    => Proxy fmt
                    -> (forall s. TracingRedex s a)
                    -> Stream (a, Derivation)
```

### User Code Example

```haskell
-- In examples/system-f/Main.hs
data SystemFStyle

instance JudgmentStyle SystemFStyle where
  formatConclusion "typeof" [ctx, e, ty] = ctx ++ " ⊢ " ++ e ++ " : " ++ ty
  formatConclusion "lookupTm" [ctx, n, ty] = ctx ++ "(" ++ n ++ ") = " ++ ty
  formatConclusion "substTy" [d, s, t, r] = "[" ++ s ++ "/" ++ d ++ "]" ++ t ++ " = " ++ r
  formatConclusion name args = defaultFormat name args

main = do
  let results = runTracingRedexWith (Proxy @SystemFStyle) $ ...
```

### Pros
- Complete user control over formatting
- No hardcoded judgment names in library
- Clean separation of concerns
- Users can have multiple formatting styles

### Cons
- Does NOT solve the variable resolution problem (still shows `x0` instead of values)
- Requires Proxy threading or ImplicitParams
- More boilerplate for users

### To Fix Variable Resolution Too

Combine with Proposal 1: capture terms, then apply substitution, then format using user's style.

---

## Proposal 3: Derivation as First-Class Data with Lazy Fields

### Idea

Make derivation nodes contain lazy thunks that close over the substitution. When the derivation is forced (for printing), variables are resolved.

### Design

```haskell
-- Derivation contains thunks that resolve when forced
data Derivation = Derivation
  { derivRule     :: String
  , derivArgs     :: IO [String]  -- Lazily resolves variables
  , derivChildren :: [Derivation]
  }

-- Or using a Reader for cleaner semantics:
data Derivation s = Derivation
  { derivRule     :: String
  , derivArgs     :: Subst s -> [String]  -- Function that resolves given final subst
  , derivChildren :: [Derivation s]
  }

-- When building derivation, capture variable references:
pushFrame name terms = modify $ \s -> s
  { tsDerivStack = frame : tsDerivStack s }
  where
    frame = DerivFrame name (mkResolver terms) []
    mkResolver terms subst = map (resolveAndPretty subst) terms

-- At the end, apply final substitution:
runTracingRedex m = do
  (result, finalSubst, rawDeriv) <- runStateT m emptyState
  let resolvedDeriv = applySubst finalSubst rawDeriv
  return (result, resolvedDeriv)
```

### Pros
- Derivations always show resolved values
- No pre-computed strings that become stale
- Works naturally with the stateful computation model

### Cons
- More complex derivation type
- Need to be careful about capturing the right substitution state
- Lazy thunks can be tricky to reason about

---

## Proposal 4: Complete Rewrite with Explicit Derivation Effect

### Idea

Treat derivation building as a separate effect that runs alongside (or after) the logic computation. Use a more principled effect system approach.

### Design

```haskell
-- Separate the computation from the derivation building
data TracingRedex s a = TracingRedex
  { runLogic :: StateT (LogicState s) Stream a
  , runDeriv :: Writer [DerivEvent] ()
  }

data DerivEvent
  = EnterRule String [CapturedTerm]
  | ExitRule String
  | UnifyEvent VarId Term Term  -- Track unifications for resolution

-- Build derivation tree from event stream + final substitution
buildDerivation :: [DerivEvent] -> Subst -> Derivation
buildDerivation events subst = foldl' processEvent emptyStack events
  where
    processEvent stack (EnterRule name terms) = push (resolveTerms subst terms) stack
    processEvent stack (ExitRule _) = pop stack
    -- etc.
```

### Alternative: Post-hoc Resolution

Run the logic computation first, then replay with derivation tracking:

```haskell
-- Phase 1: Pure logic computation, returns substitution
runLogicOnly :: (forall s. Redex (LogicOnly s) => Redex a) -> Stream (a, Subst)

-- Phase 2: Replay with derivation tracking using final substitution
replayWithDeriv :: Subst -> (forall s. ...) -> Derivation
```

### Pros
- Clean separation of concerns
- Each effect handled independently
- Easier to reason about

### Cons
- Major architectural change
- May duplicate computation (if replaying)
- More complex types

---

## Proposal 5: Substitution-Aware Pretty Printing via deref

### Idea

Instead of capturing pretty-printed strings, capture "pretty-print actions" that call `deref` at render time.

### Design

```haskell
-- A deferred pretty-print action
type PrettyAction rel = rel String

-- Modified judgment to capture actions instead of strings
judgment2 _ rules x y = Applied2 (x, y) $ argument2 x y $ \x' y' ->
  let actions = [prettyResolved x', prettyResolved y']  -- Actions, not strings!
  in ...

-- prettyResolved does deref + pretty
prettyResolved :: (RedexEval rel, LogicType a) => L a rel -> rel String
prettyResolved term = do
  resolved <- eval term  -- Dereference to ground value
  return $ prettyGround resolved

-- TracingRedex stores actions and runs them at the end
data DerivFrame rel = DerivFrame
  { frameName    :: String
  , frameActions :: [rel String]  -- Deferred pretty-print actions
  , frameChildren :: [Derivation]
  }

-- When popping frame, run the actions to get strings
popFrame :: TracingRedex s ()
popFrame = do
  frame <- popCurrentFrame
  args <- sequence (frameActions frame)  -- Run the deferred actions NOW
  let deriv = Deriv (frameName frame) args (frameChildren frame)
  addToParent deriv
```

### Problem

This doesn't quite work because `eval` requires the variable to be BOUND, but we want to capture the term BEFORE execution (when the frame is created), then resolve it AFTER execution (when the frame is popped).

### Revised Design

```haskell
-- Capture variable references, not values or strings
data DerivFrame s = DerivFrame
  { frameName    :: String
  , frameVars    :: [SomeVar s]  -- The actual variables
  , frameChildren :: [Derivation]
  }

data SomeVar s where
  SomeVar :: LogicType a => Var a (RVar (TracingRedex s)) -> SomeVar s

-- When popping, read current values of those variables
popFrame :: TracingRedex s ()
popFrame = do
  frame <- popCurrentFrame
  subst <- gets tsSubst
  let args = map (resolveVar subst) (frameVars frame)
  ...
```

### Pros
- Works with existing substitution model
- No existential types for terms (just for variables)
- Clean: "what are the variables?" is separate from "what are their values?"

### Cons
- Only captures Free variables, not Ground terms in arguments
- Need to handle mixed Free/Ground arguments
- Adds complexity to frame management

---

## Recommendation

**Proposal 1 (Deferred Pretty-Printing) + Proposal 2 (User Formatter)** together address both issues:

1. **Capture CapturedTerms** in Relation and DerivFrame instead of strings
2. At render time, **apply final substitution** to resolve all variables
3. User provides **JudgmentFormatter** typeclass instance for their domain

This gives:
- Resolved values in derivations (not `x0`, `x1`)
- User-controlled formatting (not hardcoded in library)
- Minimal API changes for defining relations

### Implementation Sketch

```haskell
-- 1. CapturedTerm existential
data CapturedTerm rel where
  CapturedTerm :: LogicType a => L a rel -> CapturedTerm rel

-- 2. Modified Relation stores terms
data Relation rel = Relation
  { relName  :: String
  , relTerms :: [CapturedTerm rel]
  , relBody  :: rel ()
  }

-- 3. TracingRedex stores terms in frames
data DerivFrame s = DerivFrame
  { frameName     :: String
  , frameTerms    :: [CapturedTerm (TracingRedex s)]
  , frameChildren :: [Derivation]
  }

-- 4. Derivation is pure data (strings, not terms)
data Derivation = Deriv String [String] [Derivation]

-- 5. Resolution happens at popFrame time
popFrame = do
  frame <- popCurrentFrame
  args <- mapM resolveCaptured (frameTerms frame)  -- Deref NOW
  let deriv = Deriv (frameName frame) args (reverse $ frameChildren frame)
  addToParent deriv

resolveCaptured :: CapturedTerm (TracingRedex s) -> TracingRedex s String
resolveCaptured (CapturedTerm term) = prettyResolved term

-- 6. User formatter (provided in examples, not library)
class JudgmentFormatter where
  format :: String -> [String] -> String

-- 7. prettyDerivation takes formatter
prettyDerivation :: JudgmentFormatter fmt => Proxy fmt -> Derivation -> String
```

### Migration Path

1. Add `CapturedTerm` and modify `Relation` (backwards compatible with wrapper)
2. Update TracingRedex to use terms instead of strings
3. Add resolution in `popFrame`
4. Create `JudgmentFormatter` typeclass
5. Move hardcoded formatting from TracingRedex to examples
6. Update examples to provide formatter instances
