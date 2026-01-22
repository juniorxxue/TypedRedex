  ## Alternative B: Search tree API (more general)

  Define a generic “search tree” for goal execution:

  data Search a
    = Fail Failure
    | Success a
    | Choice [Search a]

  - Eval just collects all Success.
  - Trace picks the leftmost path, and if it ends in Fail, renders the partial derivation from that path.

  This is more general but more invasive; Proposal A is simpler and keeps Goal execution unchanged.
