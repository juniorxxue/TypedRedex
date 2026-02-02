<script src="https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.9.0/languages/haskell.min.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.9.0/languages/scheme.min.js"></script>

{.title}
# <h1 class="title">TypedRedex</h1>


<div style="text-align: center; margin-top: 1em;">
<p style="font-size: 1.5em; color: #555;">Typed embedded Redex in Haskell</p>
</div>

<div style="text-align: center; margin-top: 2em;">
<p style="font-size: 1.3em; font-weight: 500;">Xu Xue</p>
</div>

{pause up}

# Agenda

**Part I: Background**

1. PLT Redex overview
2. Pain points of Redex in practice

{pause}

**Part II: TypedRedex**

3. The same workflow, but in Haskell
4. What's more

{pause}

**Part III: Under the Hood**

5. Implementation
6. Case study
7. Conclusion & future work

{pause up}

---

{.section}
# Part I: Background

{pause up}

# PLT Redex: What is it?

* *A Racket DSL for modeling programming language semantics*

{pause}

* *A lightweight mechanisation on top of property-based testing*

{pause}


**Recent uses**

Blame-Correct Support for Receiver Properties in Recursively-Structured Actor Contracts
*Vandenbogaerde, Stiévenart, De Roover (2024)*

Verifying Rust Implementation of Page Tables in a Software Enclave Hypervisor
*Dai, Liu, Sjoberg, Li, Chen, Wang, Jia, Anderson, Elbeheiry, Sondhi, Zhang, Ni, Yan, Gu, He (2024)*

The Fearless Journey
*Webster, Servetto, Homer (2024 (arXiv))*

Secure RDTs: Enforcing Access Control Policies for Offline Available JSON Data
*Renaux, Van den Vonder, De Meuter (2023)*

A Formal Model of Checked C
*Li, Liu, Postol, Lampropoulos, Van Horn, Hicks (2022)*

{pause up}

## Typical workflow

1. **Define** syntax and judgments/relations.
2. **Execute** them on concrete terms
3. **Test** meta-theory with random program generation
4. **Typeset** generate PDF to share

{pause up}

# Running Example: STLC

We use a simply-typed lambda calculus (STLC) throughout:

| Component | Definition |
|-----------|------------|
| **Types** | `Int` \| `A → B` |
| **Terms** | variables, λ-abstractions, application, integers |

{pause}

**Judgments:**

- `typeof(Γ, t, τ)` — typing relation
- `step(t, t')` — small-step operational semantics

{pause up}

# 1. Defining Syntax

```scheme
(define-language STLC
  (e (e e)
     x
     (λ (x τ) e)
     (if0 e e e)
     (+ e e)
     number)
  (τ (τ -> τ) num)
  (x variable-not-otherwise-mentioned))
```

{pause}

**Notes:**

1. Grammar-based syntax definitions

{pause}

2. Use `redex-match` to test the grammar

```scheme
(redex-match STLC e (term (λ (x num) 1)))
```

{pause}

3. Built-in support for binding and variables

{pause up}

# 2. Defining a Judgment (Typing)

<div style="display: flex; gap: 1em;">
<div style="flex: 1;">

```scheme
(define-judgment-form STLC
  #:mode (typeof I I O)
  #:contract (typeof Γ e τ)

  [---------------------
   (typeof Γ number num)]

  [(typeof Γ e_1 num)
   (typeof Γ e_2 num)
   --------------------------
   (typeof Γ (+ e_1 e_2) num)]

  [(typeof Γ e_1 num)
   (typeof Γ e_2 τ)
   (typeof Γ e_3 τ)
   ------------------------------
   (typeof Γ (if0 e_1 e_2 e_3) τ)]
```

</div>
<div style="flex: 1;">

```scheme
  [(where τ (lookup Γ x))
   ----------------------
   (typeof Γ x τ)]

  [(typeof Γ e_1 (τ_2 -> τ))
   (typeof Γ e_2 τ_2)
   --------------------------
   (typeof Γ (e_1 e_2) τ)]

  [(typeof (x_1 τ_1 Γ) e τ)
   ----------------------------------------
   (typeof Γ (λ (x_1 τ_1) e) (τ_1 -> τ))])
```

</div>
</div>

{pause}

**Notes:**

1. use `:mode` to specify *modes*
2. use `:contract` to specify *contracts* (syntax-check on caller site).
1. use `e_1, e_2, ...` to declare meta-variables
2. use `where` to declare a equality.

{pause up}

# 3. Running Judgments

```scheme
(define (typecheck G e)
  (match (judgment-holds (typeof ,G ,e τ) τ)
    [(list) #f]
    [(list t) t]
    [_ (error 'typecheck
              "multiple typing derivations for term ~a in environment ~a"
              e G)]))
```

{pause}

**Eval to a result**
```scheme
(typecheck (term ·) (term 1))
;; => (term num))
```

{pause}
**Inspect the derivation**
```scheme
(build-derivations (typeof (term ·) (term 1) τ))
```

{pause up}
# 4. Property-based testing
```scheme
(define (preservation e)
  (define types (judgment-holds (typeof · ,e τ) τ))
  (unless (null? types)
    (unless (= 1 (length types)) (error 'preservation "multiple types! ~s" e)))
  (cond
    [(null? types) #t]
    [else
     (for/and ([v (apply-reduction-relation* red e)])
       (equal? (judgment-holds (typeof · ,v τ) τ)
               types))]))
```

Random generation in Redex is a huge amount of work

{pause up}

# Pain Points of Redex (in practice)

Common friction points:

* **Untyped meta-language**: Errors discovered late (often deep in evaluation)
 * Needs `redex-match` to check that a expression matches a grammer or not
* **No static checking**: Arity, modes, contracts checked only at runtime
* **Opaque failures**: Hard to see *where* a derivation got stuck
* **Ad-hoc typesetting**: no support for customization or code escape

{pause up}

---

{.section}
# Part II: TypedRedex

{pause up}

# TypedRedex: The Pitch

*Embedded in Haskell*

{pause}

*Rules as a typed AST*

{pause}

*Multiple interpreters*

{pause}

*Modern logic solver under the hood*

{pause}

**Design goals:**

- ✓ The Redex workflow, but with Haskell's static types (more static guarantee)
- ✓ Reusable interpreters over the same rule AST
- ✓ Better failure information
- ✓ Native binding support
- ✓ Property testing via QuickCheck

{pause up}

# TypedRedex: Defining Syntax

1. Define systax in plain Haskell ADTs

```haskell
data Ty = TyInt | TyBool | TyArr Ty Ty

data Tm
  = TmVar Nom
  | Lit Nat
  | Lam Ty (Bind Nom Tm)
  | App Tm Tm
  | Plus Tm Tm
  | BTrue
  | BFalse
  | If Tm Tm Tm

data Env = EEmpty | EBind Nom Ty Env
```

`Bind` and `Nom` are built-in support of binders

{pause up}

2. Provide Repr instances for embedding into terms
```haskell
instance Repr Ty where
  data Reified Ty
    = RTInt
    | RTArr (Logic Ty) (Logic Ty)

project TInt = RTInt
project (TArr a b) = RTArr (Ground (project a)) (Ground (project b))

reify RTInt = Just TInt
reify (RTArr (Ground a) (Ground b)) = TArr <$> reify a <*> reify b
```

- `Reified` expressions is indexed by `Ty`
- `Logic` expressions has two instances: `Ground` and `LogicVar`

{pause up}

3. Provide naming for pretty printing

```haskell
instance Pretty Ty where
  varNames = cycleNames ["A", "B", "C", "D"]
  prettyReified RTInt = pure "int"
  prettyReified (RTArr a b) = do
    da <- prettyLogic a
    db <- prettyLogic b
    pure (parens (da <+> Doc " -> " <+> db))
```

{pause}
4. Provide smart constructors used in DSL

```haskell
tint :: Term Ty
tint = ground TInt

tarr :: Term Ty -> Term Ty -> Term Ty
tarr = lift2 (\a b -> Ground (RTArr a b))
```

{pause}

**Notes:**
- All 2. 3. 4. can be automated by Template Haskell
- Users only need to provide plain AST and names of smart construtors (small-case)

{pause up}

# TypedRedex: Defining Judgments

```haskell
typeof :: Judgment "typeof" '[I, I, O] '[Env, Tm, Ty]
typeof = judgment $
  format (\env tm ty -> env <+> " ⊢ " <+> tm <+> " : " <+> ty)
  >>
  rules
    [ rule "Ty-Int" $ do
        (g, n) <- fresh
        concl $ typeof g (lit n) tint

    , rule "Ty-Var" $ do
        (g, x, ty) <- fresh
        prem  $ lookup g x ty
        concl $ typeof g (var x) ty

    , rule "Ty-App" $ do
        (g, t1, t2, a, b) <- fresh
        prem  $ typeof g t1 (tarr a b)
        prem  $ typeof g t2 a
        concl $ typeof g (app t1 t2) b
    ]
```

{pause up}

# What the Type Signature Gives You

```haskell
typeof :: Judgment "typeof" '[I, I, O] '[Env, Tm, Ty]
--                 ^^^^^^^^  ^^^^^^^^^  ^^^^^^^^^^^^^
--                 name      modes      argument types
```

{pause}

**Static guarantees:**

1. Judgment name at the type level → unique identification
2. Mode list (`I`/`O`) at the type level
  - possible to be checked at compile time
3. Argument types → arity and type mismatches caught early

{pause up}

# TypedRedex: Running a Judgment

We can always derive a plain Haskell function (no logics involved).

```haskell
infer0 :: Tm -> [Ty]
infer0 tm = eval $ query $ do
  ty <- qfresh
  pure (typeof eempty (ground tm) ty, ty)

step1 :: Tm -> [Tm]
step1 tm = eval $ query $ do
  tm' <- qfresh
  pure (step (ground tm) tm', tm')
```

{pause}

**Same Redex workflow:**

1. Build a query with unknowns (logic variables)
2. Evaluate to get zero or more answers
3. Results are ordinary Haskell values

{pause up}

# TypedRedex: Property Testing

Determinism: at most one type for any well-typed term

```haskell
prop_progress :: WT -> Property
prop_progress (WT expected tm) =
  case infer0 tm of
    [ty] | ty == expected ->
      withCoverage tm $
        isValue tm || not (null (step1 tm))
    _ -> counterexample "generator/typechecker mismatch" False

prop_preservation :: WT -> Property
prop_preservation (WT expected tm) =
  case infer0 tm of
    [ty] | ty == expected ->
      withCoverage tm $
        conjoin [ infer0 tm' == [ty] | tm' <- step1 tm ]
    _ -> counterexample "generator/typechecker mismatch" False
```

1. Use QuickCheck to generate random (closed) terms
2. The library itself stays QuickCheck-agnostic

{pause}

Integrates naturally with the Haskell testing ecosystem.

{pause up}

# Feature: Mode Checking

TypedRedex provides a mode-checking interpreter:

```haskell
import TypedRedex.Interp.MCheck (mcheck)

-- Analyze a judgment without running it
putStrLn (mcheck typeof)
```

{pause}

**Catches issues like:**

- **Ghost outputs** — outputs that are never produced
- **Unschedulable premises** — cannot be evaluated from available inputs
- **Ambiguous premise order** — (optional verbose mode)

{pause up}

# Feature: Customizable Typesetting

Generate inference rules from judgment definitions:

```haskell
import TypedRedex.Interp.Typeset (typeset)

putStrLn (typeset infer)
```

{pause}

**Output excerpt:**

```text
Γ (x) = A
--------- T-Var
Γ ⊢ x : A

Γ, x:A ⊢ e : B
---------------------- T-Abs
Γ ⊢ \x : A. e : A -> B

Γ ⊢ e : B -> A    Γ ⊢ e1 : B
---------------------------- T-App
Γ ⊢ (e e1) : A
```

1. Configurations in `Pretty` instance of ASTs and `format` of judgments.
2. Able to export Latex code with cross-reference.

{pause up}

# Feature: Partial Derivations

In PL research, rules are often "almost right."

{pause}

**When a query fails, you want to know:**

- Which rule was selected?
- Which premise failed?
- What was derived *before* the failure?

{pause}

**Redex:** "No answers." (and good luck debugging)

**TypedRedex:**

1. Returns a partial derivation tree showing exactly where it got stuck.
2. Displaying the matched rule in the process, in case of non-terminating.

{pause}

**Plain Haskell:**
- `Debug.Trace` to print, but painful.
- Need a feature logs "which pattern is matched".

{pause up}

# Feature: Partial Derivations — Example

This example will fail in the middle of type-checking `1 + true`.

```text
if (\x:Bool. \y:Int. 1 + true) true 1 then 1 else 2
```
{pause}
call the trace interpreter:
```haskell
let qTypeof = query $ do
      ty <- qfresh
      pure (typeof eempty expr ty, ty)
printTrace _ (trace qTypeof)
```
{pause}

```text
---------------------------------------------------------------------------------------------------- [<no matching rule>]
., x:bool, y:int ⊢ (S(0) + true) : bool [FAIL: head failed: ., x:bool, y:int ⊢ (S(0) + true) : bool]
------------------------------------------------------------------------------------------------------------------------- [T-Abs]
                                    ., x:bool ⊢ \y : int. (S(0) + true) : int -> bool
--------------------------------------------------------------------------------------------------------------------------------- [T-Abs]
                                   . ⊢ \x : bool. \y : int. (S(0) + true) : bool -> ? -> bool                                               . ⊢ true : ? (skipped)
------------------------------------------------------------------------------------------------------------------------------------------------------------------ [T-App]
                                                    . ⊢ (\x : bool. \y : int. (S(0) + true) true) : ? -> bool                                                                . ⊢ S(0) : ? (skipped)
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- [T-App]
                                                                    . ⊢ ((\x : bool. \y : int. (S(0) + true) true) S(0)) : bool                                                                               . ⊢ S(0) : ? (skipped)   . ⊢ S(S(0)) : ? (skipped)
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- [T-If]
                                                                                       . ⊢ if ((\x : bool. \y : int. (S(0) + true) true) S(0)) then S(0) else S(S(0)) : ?
```

{pause}

Shows exactly where derivation stopped → tune the next rule.

{pause up}

---

{.section}
# Part III: Under the Hood

**Design goals:**

1. The Redex workflow, but with Haskell's static types (more static guarantee)
2. Reusable interpreters over the same rule AST
3. Better failure information
4. Native binding support
5. Property testing via QuickCheck

{pause}
**Solutions:**
1. Higher-kinded types
2. Free Monad for deep embedding
3. Novel operational semantics for unification solving
4. Nominal unification
5. Escape to normal Haskell code (normal AST and function)

{pause up}

# Architecture Overview

```text
┌─────────────────────────────────────────────────────────────┐
│                     DSL Layer (RuleM)                       │
└──────────────────────────┬──────────────────────────────────┘
                           │ build
                           ▼
┌─────────────────────────────────────────────────────────────┐
│              Rule AST (Free monad over RuleF)               │
└───────┬─────────────┬─────────────┬─────────────┬───────────┘
        │             │             │             │
        ▼             ▼             ▼             ▼
   ┌─────────┐  ┌──────────┐  ┌──────────┐  ┌─────────┐
   │  eval   │  │  trace   │  │ typeset  │  │ mcheck  │
   └────┬────┘  └────┬─────┘  └────┬─────┘  └────┬────┘
        │            │             │             │
        ▼            ▼             ▼             ▼
    [answers]   derivation     inference      mode
                  trees          rules       analysis
```

{pause up}

# Free Monad Core

Rules are **data**, not functions:

```ocaml
-- Indexed free monad over RuleF
type RuleM ts a = IxFree (RuleF ts) () () a

data RuleF ts s t a where
  FreshF  :: RuleF ts s s (Term a)          -- fresh logic var
  ConclF  :: JudgmentCall ... -> RuleF ...  -- conclusion
  PremF   :: JudgmentCall ... -> RuleF ...  -- premise
  EqF     :: Term a -> Term a -> RuleF ...  -- unification
  HashF   :: Term n -> Term t -> RuleF ...  -- freshness (#)
  GuardF  :: RuleM ts () -> RuleF ...       -- side condition
  NegF    :: Rule name ts' -> RuleF ...     -- negation-as-failure
```

{pause}

**Key insight:** Same rule definition → multiple interpretations.

{pause up}

# Eval Interpreter: Search Pipeline

```
Rule AST
    │
    ▼ translate
miniKanren Goal AST
    │
    ▼ execute
Search with:
  • Nominal unification (α-equivalence)
  • Freshness constraints (name ∉ term)
  • Fair scheduling (interleaved disjunctions)
    │
    ▼
[Answer₁, Answer₂, ...]
```

{pause up}

# Demo: LCTI Case Study

The repository includes a larger example:

```bash
cabal run example-lcti
```

{pause}

**What it demonstrates:**

| Feature | Example |
|---------|---------|
| Complex judgment | `infer` with many rules and modes |
| Regression suite | 133 test cases in current harness |
| Typesetting | Automatic inference rule generation |
| Debugging | Partial derivations for failing tests |

{pause up}

---

{.section}
# Conclusion

{pause up}

# Summary

**TypedRedex provides:**

| Feature | Benefit |
|---------|---------|
| Typed judgments | Catch errors at compile time |
| Multiple interpreters | Same rules → eval, trace, typeset, mcheck |
| Partial derivations | See exactly where derivations fail |
| Mode checking | Static analysis of judgment modes |
| Customizable rendering | Generate paper-ready inference rules |

{pause up}

# Future Work

**Syntax:**
- Order-sensitive rules
- More preludes: arithmetic, booleans, lists, etc.

**Ergonomics:**

- More syntax helpers for `Repr` and standard containers
- Better error messages from type-level information

**Tooling:**

- QuickCheck generators for common AST patterns
- Streaming debug mode (live derivation trees)
- IDE integration (hover for inferred modes)

{pause up}

# References

**Embedding and DSLs:**
1. Combining Deep and Shallow Embedding for EDSL
2. Typed Tagless Final Interpreters

**Higher-kinded types:**
1. Logic Programming with Extensible Types
2. Typed Embedding of miniKanren for Functional Conversion

**Minikanren implementations:**
1. Constructive Negation for MiniKanren
2. A Fresh Name in Nominal Logic Programming
3. µKanren: A Minimal Functional Core for Relational Programming
4. Visualizing miniKanren Search with a Fine-Grained Small-Step Semantics

**PLT Redex:**
1. Redex2Coq: towards a theory of decidability of Redex's reduction semantics
2. Randomized Testing in PLT Redex
3. An Overview of Property-Based Testing for the Working Semanticist