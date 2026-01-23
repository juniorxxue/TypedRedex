  ## Alternative B: Search tree API (more general)

  Define a generic “search tree” for goal execution:

  data Search a
    = Fail Failure
    | Success a
    | Choice [Search a]

  - Eval just collects all Success.
  - Trace picks the leftmost path, and if it ends in Fail, renders the partial derivation from that path.

  This is more general but more invasive; Proposal A is simpler and keeps Goal execution unchanged.

  ## Nominal unification notes

  - Fresh-name supply: `freshName` is a global counter that does not track names already present in a goal.
    Current workaround is to start `substNextName` at 1000 in `emptySubst` to avoid collisions with small
    ids used in preEnv (`TyNom 0/1`). This is not principled; a real fix would require a freshness supply
    relative to the current goal (or nominal suspensions).
  - Theory caveat: unification implements the standard nominal step with freshness constraints, but the
    system does not support suspensions, so it cannot push swaps through non-ground bodies. This is fully
    correct for the cases we hit where one side is ground, but it is not a complete nominal unifier. If
    full nominal unification is needed, we should plan that explicitly.
