# shallow-kanren-minimal

Minimal standalone extraction of the *typed shallow miniKanren embedding* from the
`uKanren_transformations` `shallow-embedding` branch.

This package includes:

- The typed/tagless-final DSL (`Shallow.Core.*`, `Shallow.Utils.*`)
- A small interpreter with substitution + streams (`Shallow.Interpreters.SubstKanren`)
- Runnable examples in `examples/` demonstrating various type systems and operational semantics

## Building

Build all examples (from this directory):

```sh
cabal build
```

## Examples

### 1. Lambda Calculus Small-Step Semantics (`examples/lambda-step/`)
Small-step call-by-value operational semantics for lambda calculus with de Bruijn indices.

```sh
cabal run example-lambda-step
```

### 2. Bidirectional Typing for STLC (`examples/stlc-bidir/`)
Implements Dunfield & Krishnaswami-style bidirectional type checking with synthesis (⇒) and checking (⇐) modes.

```sh
cabal run example-stlc-bidir
```

### 3. Hindley-Milner Type Inference (`examples/hm-inference/`)
Simplified HM type inference (Algorithm W style) with monomorphic types.

```sh
cabal run example-hm-inference
```

### 4. PCF with Fixpoints (`examples/pcf-step/`)
Small-step operational semantics for Programming Computable Functions (PCF) with natural numbers, conditionals, and fixpoint recursion.

```sh
cabal run example-pcf-step
```

### 5. Context-Based Type Inference (LCTI) (`examples/poly-infer/`)
Faithful implementation of context-based type inference with polarized subtyping, based on the LCTI algorithm. Currently implements core features (simple types, arrows, polarity) with plans to extend to full polymorphism.

```sh
cabal run example-poly-infer
```

## Features

All examples demonstrate:
- Relational specifications of type systems and operational semantics
- Bidirectional querying (inference and synthesis)
- De Bruijn indices for variable binding
- Multiple typing/reduction rules via `conde`
