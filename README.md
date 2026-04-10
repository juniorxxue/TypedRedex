# TypedRedex

[![CI](https://github.com/juniorxxue/TypedRedex/actions/workflows/ci.yml/badge.svg)](https://github.com/juniorxxue/TypedRedex/actions/workflows/ci.yml)

TypedRedex is a Haskell library for defining Redex-style judgments, reduction rules, and semantic relations as a typed AST.

The pitch is simple:

- the Redex workflow, but embedded in Haskell
- rules represented as a typed AST
- multiple interpreters over the same rule definition
- better failure information when a derivation gets stuck

## Why TypedRedex

PLT Redex is a great environment for prototyping programming-language semantics, but in practice some common pain points remain:

- many mistakes are discovered only at runtime
- arity, mode, and contract issues are easy to encode accidentally
- failures can collapse to "no answers"
- it can be hard to inspect where a derivation stopped

TypedRedex keeps the same general workflow while leaning on Haskell's type system and tooling.

## What It Provides

TypedRedex provides:

- typed judgments with type-level names, modes, and argument types
- reusable interpreters over the same rule AST
- partial derivation trees for failed queries
- mode checking for scheduling and output-discipline issues
- customizable rule rendering for papers and notes
- nominal support for binders and freshness constraints
- natural integration with QuickCheck and ordinary Haskell code

## Workflow

A typical workflow looks like this:

1. Define object-language syntax as ordinary Haskell data types.
2. Define judgments and rules with `TypedRedex.DSL`.
3. Build queries with fresh logic variables.
4. Choose an interpreter depending on whether you want answers, traces, typeset rules, or mode analysis.

## Example

The STLC example in this repository defines typing as a typed judgment:

```haskell
typeof :: Judgment "typeof" '[I, I, O] '[Env, Tm, Ty]
typeof = judgment $
  format (\env tm ty -> env <+> " ⊢ " <+> tm <+> " : " <+> ty)
  P.>> rules
    [ rule "T-Var" $ do
        (env, x, ty) <- fresh
        prem  $ lookupVar env x ty
        concl $ typeof env (var x) ty

    , rule "T-Abs" $ do
        (env, x, tyA, body, tyB) <- fresh
        prem  $ typeof (ebind x tyA env) body tyB
        concl $ typeof env (lam tyA x body) (tarr tyA tyB)

    , rule "T-App" $ do
        (env, t1, t2, tyA, tyB) <- fresh
        prem  $ typeof env t1 (tarr tyA tyB)
        prem  $ typeof env t2 tyA
        concl $ typeof env (app t1 t2) tyB
    ]
```

The type already carries three important pieces of information:

- the judgment name
- the mode list
- the argument types

That means many shape errors are pushed earlier, into Haskell's type checking, instead of being left entirely to runtime.

## Interpreters

TypedRedex ships with several interpreters over the same rule AST.

| Module | Purpose |
| --- | --- |
| `TypedRedex.Backend.Eval` | Run queries and collect answers |
| `TypedRedex.Interp.Trace` | Return successful or failing derivation trees |
| `TypedRedex.Interp.Typeset` | Render rules for notes and papers |
| `TypedRedex.Interp.MCheck` | Analyze mode discipline and scheduling |

## Failure Traces

One of the main goals of the library is to make failures more informative.

Instead of only getting an empty result, the trace interpreter can show which rule matched, which premise failed, and how far the derivation progressed before getting stuck.

This is especially useful while tuning a semantics or debugging a rule set.

## Included Examples

The repository currently includes two runnable examples.

- `STLC`: simply typed lambda calculus with tracing and QuickCheck properties
- `LCTI`: a larger inference-oriented case study with a regression suite

Run them with:

```bash
cabal run example-stlc
cabal run example-lcti
```

## Installation

TypedRedex is currently intended to be used from a source checkout.

```bash
cabal update
cabal build
```

To build the library and the included executables:

```bash
cabal build all
```

## Modules

- `TypedRedex.DSL`: user-facing DSL for judgments and rules
- `TypedRedex.Backend.*`: query construction and evaluation backend
- `TypedRedex.Interp.*`: tracing, typesetting, and mode checking
- `TypedRedex.Nominal*`: binder-oriented utilities and nominal support
- `TypedRedex.Core.*`: internal typed AST and supporting infrastructure

## Roadmap

- Use Template Haskell to generate routine syntax definitions automatically, while still letting users define binder-heavy or otherwise non-standard cases by hand.
- Add an interactive front end for building derivations by selecting rules, in the spirit of [Hazel Deriver](https://arxiv.org/abs/2506.10781). This would support reasoning with rule systems that are not purely algorithmic, and would likely take the form of a new interpreter.

## Status

TypedRedex is currently experimental.

The implementation is usable and the examples are non-trivial, but the public API should still be treated as evolving.

## Contributing

Contribution guidelines live in [`CONTRIBUTING.md`](CONTRIBUTING.md).

## License

TypedRedex is released under the MIT License. See [`LICENSE`](LICENSE).
