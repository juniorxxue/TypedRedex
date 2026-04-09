# TypedRedex

[![CI](https://github.com/juniorxxue/TypedRedex/actions/workflows/ci.yml/badge.svg)](https://github.com/juniorxxue/TypedRedex/actions/workflows/ci.yml)

TypedRedex is a Haskell library for defining Redex-style judgments, reduction rules, and semantic relations as a typed AST.

It is designed for language prototyping and semantics engineering in a style that stays close to Redex while fitting naturally into the Haskell toolchain.

## Features

- typed judgments with type-level names, modes, and argument lists
- multiple interpreters over the same rule definition
- ordinary Haskell syntax trees instead of a separate meta-language
- partial derivation traces for debugging failed queries
- mode checking for scheduling and output-discipline issues
- nominal support for binders and freshness constraints
- straightforward integration with the Haskell ecosystem, including QuickCheck

## Installation

TypedRedex is currently intended to be used from a source checkout.

```bash
cabal update
cabal build
```

To build the library and the included example executables:

```bash
cabal build all
```

## Quick Start

The main entry point is [`TypedRedex.DSL`](src/TypedRedex/DSL.hs).

A judgment is defined once, then reused by different interpreters.

```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QualifiedDo #-}

import qualified TypedRedex.DSL as R
import TypedRedex.Backend.Eval (eval, query, qfresh)

add :: R.Judgment "add" '[R.I, R.I, R.O] '[Nat, Nat, Nat]
add = R.judgment $
  R.rules
    [ R.rule "add-zero" $ R.do
        y <- R.fresh
        R.concl $ add zro y y

    , R.rule "add-succ" $ R.do
        (x, y, z) <- R.fresh
        R.prem $ add x y z
        R.concl $ add (suc x) y (suc z)
    ]

plusOne :: Nat -> [Nat]
plusOne n = eval $ query $ do
  out <- qfresh
  pure (add (R.ground n) (R.ground (S Z)) out, out)
```

For complete examples with syntax definitions, pretty-printing, binders, tracing, and property tests, start with [`examples/projects/STLC`](examples/projects/STLC) or [`examples/projects/LCTI`](examples/projects/LCTI).

## Interpreters

TypedRedex ships with several interpreters over the same rule AST.

| Module | Purpose |
| --- | --- |
| `TypedRedex.Backend.Eval` | Run queries and collect answers |
| `TypedRedex.Interp.Trace` | Return successful or failing derivation trees |
| `TypedRedex.Interp.Typeset` | Render rules for notes and papers |
| `TypedRedex.Interp.MCheck` | Analyze mode discipline and scheduling |

## Module Guide

- `TypedRedex.DSL`: user-facing DSL for judgments and rules
- `TypedRedex.Core.*`: internal typed AST and supporting infrastructure
- `TypedRedex.Backend.*`: query construction and evaluation backend
- `TypedRedex.Interp.*`: tracing, typesetting, and mode checking
- `TypedRedex.Nominal*`: binder-oriented utilities and nominal support

## Examples

The repository currently includes two runnable examples.

- `STLC`: simply typed lambda calculus with tracing and QuickCheck properties
- `LCTI`: a larger inference-oriented case study

Run them with:

```bash
cabal run example-stlc
cabal run example-lcti
```

## Development

CI runs the following checks on GitHub Actions:

- `cabal check`
- `cabal build all`
- `cabal run example-stlc`
- `cabal run example-lcti`
- `cabal sdist`

Contribution guidelines live in [`CONTRIBUTING.md`](CONTRIBUTING.md).

## Status

TypedRedex is currently experimental.

The implementation is usable and the examples are non-trivial, but the public API should still be treated as evolving.

## License

TypedRedex is released under the MIT License. See [`LICENSE`](LICENSE).
