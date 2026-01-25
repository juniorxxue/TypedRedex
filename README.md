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

  ## Nominal unification notes

  - Fresh-name supply: `freshName` is a global counter that does not track names already present in a goal.
    Current workaround is to start `substNextName` at 1000 in `emptySubst` to avoid collisions with small
    ids used in preEnv (`TyNom 0/1`). This is not principled; a real fix would require a freshness supply
    relative to the current goal (or nominal suspensions).
  - Theory caveat: unification implements the standard nominal step with freshness constraints, but the
    system does not support suspensions, so it cannot push swaps through non-ground bodies. This is fully
    correct for the cases we hit where one side is ground, but it is not a complete nominal unifier. If
    full nominal unification is needed, we should plan that explicitly.
