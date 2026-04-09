# TypedRedex

[![CI](https://github.com/juniorxxue/TypedRedex/actions/workflows/ci.yml/badge.svg)](https://github.com/juniorxxue/TypedRedex/actions/workflows/ci.yml)

TypedRedex is a Haskell library for defining Redex-style judgments, reduction rules, and semantic relations as a typed AST.

It is aimed at language prototyping and semantics engineering in a style that stays close to Redex, while fitting naturally into the Haskell toolchain.

## Features

- typed judgments with type-level names, modes, and argument lists
- multiple interpreters over the same rule definition
- ordinary Haskell syntax trees instead of a separate meta-language
- partial derivation traces for debugging failed queries
- mode checking for scheduling and output-discipline issues
- nominal support for binders and freshness constraints
- easy integration with the rest of the Haskell ecosystem, including QuickCheck

## Installation

TypedRedex is not on Hackage yet.

Today, the intended way to use it is from a source checkout:

```bash
cabal update
cabal build
```

To build everything in this repository, including the example executables:

```bash
cabal build all
```

The project is currently tested with GHC 9.6.7 and `cabal-install` 3.14.

A Hackage release is planned later, once the public API settles a bit more.

## Quick Start

The core entry point is [`TypedRedex.DSL`](src/TypedRedex/DSL.hs).

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

That snippet is intentionally minimal. For complete examples with syntax definitions, pretty-printing, binders, tracing, and property tests, start with [`examples/projects/STLC`](examples/projects/STLC).

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

The repository includes several runnable example languages.

- `STLC`: simply typed lambda calculus with tracing and QuickCheck properties
- `LTI` and `LCTI`: larger inference-oriented case studies
- `Poly` and `PolyWeak`: polymorphism-focused experiments
- `Signal`: a larger ruleset used for typesetting and mode checking

Useful entry points:

```bash
cabal run example-stlc
cabal run example-poly
cabal run example-lcti
cabal run example-signal
```

## Package Metadata And Hackage Prep

The package metadata is being kept Hackage-friendly even before the first upload.

The repository currently includes:

- a public `README.md`
- an explicit `LICENSE`
- homepage and issue tracker links in the Cabal file
- `tested-with` information in the Cabal file
- source-distribution checks in CI via `cabal sdist`

## Development

CI runs the following checks on GitHub Actions:

- `cabal check`
- `cabal build all`
- `cabal run example-stlc`
- `cabal sdist`

Contribution guidelines live in [`CONTRIBUTING.md`](CONTRIBUTING.md).

Internal design notes and maintainer-oriented material live under [`notes/`](notes/README.md).

## Status

TypedRedex is currently an experimental library.

The implementation is usable and the examples are non-trivial, but the package should still be treated as research-oriented and evolving.

## License

TypedRedex is released under the MIT License. See [`LICENSE`](LICENSE).
