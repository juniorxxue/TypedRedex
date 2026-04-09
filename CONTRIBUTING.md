# Contributing

Thanks for your interest in TypedRedex.

This project is still research-oriented and evolving, so the most helpful contributions are usually:

- bug reports with small reproductions
- improvements to examples and documentation
- targeted fixes that keep the existing design coherent
- discussions around semantics, tracing, modes, and ergonomics

## Before Opening A Pull Request

Please run the local checks that CI expects:

```bash
cabal update
cabal check
cabal build all
cabal run example-stlc
cabal run example-lcti
cabal sdist
```

If you change the public API or the examples, please update the relevant docs as part of the same pull request.

## Development Notes

- The core library lives in `src/`.
- Runnable semantics examples live in `examples/projects/`.
- The project currently targets GHC 9.6.7.

## Style Expectations

- Keep the build warning-free.
- Prefer small, focused pull requests.
- Preserve existing example behavior unless the change is intentionally semantic.
- Add or update examples when they help explain a new behavior.

## Reporting Issues

If you open an issue, include:

- the command you ran
- the exact output or error message
- your `ghc` and `cabal` versions
- a minimal reproduction when possible

For feature requests, it helps to explain the semantics workflow you are trying to support and why the current library gets in the way.
