# TypedRedex

A typed shallow embedding of PLT Redex in Haskell using miniKanren-style logic programming.

## Project Goal

Provide a type-safe alternative to PLT Redex (Racket) for experimenting with operational semantics and type systems. The key insight: use Haskell's type system to catch errors that PLT Redex allows at runtime.

## Build & Run

```bash
# Build everything (from typed-redex/ directory)
cabal build

# Run a specific example
cabal run example-xxx

# REPL
cabal repl
```

## Research Context

- **Target venues**: ICFP, POPL, Haskell Symposium, ESOP, ECOOP
- **Novelty focus**: Type discipline for Redex-style specifications
- **Comparison**: PLT Redex uses its own solver ≈ miniKanren with ∀; TypedRedex uses miniKanren with constructive negation

## Terminology

Use "relation" (not "predicate"), "goal" (not "query"), "ground" (not "concrete").
