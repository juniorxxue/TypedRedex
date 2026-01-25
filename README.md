  ## Alternative B: Search tree API (more general)

  Define a generic “search tree” for goal execution:

  data Search a
    = Fail Failure
    | Success a
    | Choice [Search a]

  - Eval just collects all Success.
  - Trace picks the leftmost path, and if it ends in Fail, renders the partial derivation from that path.

  This is more general but more invasive; Proposal A is simpler and keeps Goal execution unchanged.

  ## Trace interpreter logic

  The trace interpreter replays judgment evaluation while building a partial derivation tree. It uses a
  search tree so it can represent matching failures separately from real errors and stop at the first
  interesting failure.

  - Search tree nodes:
    - NoMatch: head unification for a rule failed, so this rule does not apply (no derivation emitted).
    - Fail: a real failure with a partial derivation attached.
    - Success: a successful derivation.
    - Choice: nondeterministic branches from multiple rules or multiple unifiers.
  - Rule entry:
    - Collect the rule head, premises, constraints, and negations.
    - Head unification runs first; if it yields no solutions, return NoMatch (so other rules still try).
  - Premises:
    - Constraints (eq/neq/hash) run immediately; failure records a FailConstraint and marks remaining
      premises as "(skipped)" in the derivation.
    - Judgment premises recurse into the same trace search. If the premise fails, the parent rule
      becomes FailPremise, and remaining premises are skipped.
  - Negations:
    - After premises, negations are checked. Failure produces FailNegation; success adds a NegC constraint.
  - Derivation building:
    - Conclusions and constraints are rendered with the current substitution applied.
    - Failures keep the partial subtree that led to the failure, so you can inspect how far it got.
  - Trace selection:
    - The top-level `trace` returns the first successful branch if any succeed (left-to-right).
    - If no branch succeeds, it returns the deepest failing derivation (max derivation depth);
      ties are broken left-to-right.
  - Output filtering:
    - `prettyDerivationWithOmit` accepts a list of names and drops any premise derivation whose
      judgment name or rule label matches (useful for suppressing repetitive `skip-*` rules).

## Debug mode (plan)

  A streaming debug mode that prints rule-matching progress in real time, so users can see
  which rules are being attempted at each derivation level. This is especially useful when a
  program hangs — the last printed line tells you exactly where the search is stuck.

  Example output:

    1 matching eval-var, eval-app, eval-lam
    1 eval-var > lookup-here, lookup-there
    1 eval-var > lookup-here failed
    1 eval-var > lookup-there > lookup-here ...
    2   eval-app > eval-lam, eval-var
    3     eval-lam matched

  (Level number indicates derivation depth; indentation shows nesting.)

  ### Tension with current architecture

  - The Eval interpreter uses `interleave` in `exec` (Goal.hs:204) for Disj goals. This means
    branches from different rules are explored in an alternating fashion (fair scheduling), not
    strictly left-to-right. A debug trace that shows "trying Rule 1, then Rule 2" would not
    accurately reflect the actual interleaved exploration order.
  - The Trace interpreter (Trace.hs) builds the entire `Search` tree purely (no IO), then
    `selectTrace` picks the best result. It is not streaming — the tree must be fully
    constructed before any output is produced.
  - Both interpreters are pure. Adding real-time output requires introducing IO or an
    effectful layer into the core execution loop.

  ### Complexity evaluation

  Medium-to-high complexity. The main challenges are:
  1. Introducing IO (or a streaming effect) into the search loop without breaking the existing
     pure interfaces (Eval and Trace both rely on pure list/tree results).
  2. The `interleave` strategy means the "current rule being tried" is not a simple stack —
     multiple branches are live simultaneously. The debug output must either linearize this
     (losing accuracy) or show the interleaved structure (more complex output).
  3. Deciding whether debug mode should use the Eval path (accurate to what actually runs) or
     the Trace path (already has rule-level structure but is not streaming).

  ### Potential exploring directions

  - **IO-based search stepper**: Write a third interpreter (`Debug.hs`) that mirrors
    `searchJudgmentCall`/`searchRule`/`searchPremises` from Trace but runs in IO, printing
    each rule attempt as it enters. This avoids modifying the existing pure interpreters.
  - **Lazy streaming via `unsafePerformIO` / `Debug.Trace`**: Insert `Debug.Trace.trace` calls
    into the existing Trace interpreter's `searchRule` to print rule entry/exit as the Search
    tree is lazily constructed. Quick to prototype but impure and ordering depends on GHC's
    evaluation strategy.
  - **Callback/hook approach**: Parameterize `searchJudgmentCall` with a callback
    `(Int -> String -> IO ())` that is called on rule entry (depth, rule-name). The pure
    version passes a no-op; the debug version passes a printer. Requires threading the
    callback but keeps the Search tree structure intact.
  - **Depth-limited iterative deepening**: Instead of interleave, run depth-first up to depth
    N, printing attempts at each level. If no solution found, increase N. This makes debug
    output predictable (strictly left-to-right at each depth) but changes the search semantics.
  - **Streaming conduit/pipes**: Replace `[Subst]` with a streaming type (e.g., `ConduitT`
    or `ListT IO`) in the Goal executor. Each Disj node yields a "trying branch" event before
    producing results. Most invasive but most principled.
  - **Hybrid**: Use the existing Trace interpreter's Search tree but consume it incrementally —
    a `stepSearch :: Search a -> IO (Maybe (SearchEvent, Search a))` that peels off one
    Choice/Fail/Success at a time, printing as it goes. This reuses the existing tree structure
    without modifying the builder.

  ## Nominal unification notes

  - Fresh-name supply: `freshName` is a global counter that does not track names already present in a goal.
    Current workaround is to start `substNextName` at 1000 in `emptySubst` to avoid collisions with small
    ids used in preEnv (`TyNom 0/1`). This is not principled; a real fix would require a freshness supply
    relative to the current goal (or nominal suspensions).
  - Theory caveat: unification implements the standard nominal step with freshness constraints, but the
    system does not support suspensions, so it cannot push swaps through non-ground bodies. This is fully
    correct for the cases we hit where one side is ground, but it is not a complete nominal unifier. If
    full nominal unification is needed, we should plan that explicitly.

## Motivation of "guard" and analysis of order-dependence

Painful example about

```
forall b. Int -> b <: [1] -> Int
```
