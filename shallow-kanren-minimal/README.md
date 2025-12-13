# shallow-kanren-minimal

Minimal standalone extraction of the *typed shallow miniKanren embedding* from the
`uKanren_transformations` `shallow-embedding` branch.

This package includes:

- The typed/tagless-final DSL (`Shallow.Core.*`, `Shallow.Utils.*`)
- A small interpreter with substitution + streams (`Shallow.Interpreters.SubstKanren`)
- A runnable example in `app/Main.hs` (lambda-calculus small-step as a relation)

Build/run (from this directory):

```sh
cabal build
cabal run example-lambda-step
```
