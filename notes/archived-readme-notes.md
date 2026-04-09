# Archived README Notes

This file preserves the internal design notes that previously lived in the repository root `README.md` before the project was reorganized for a public release.

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

## Ordered Combinator

This is a proposal to add an *ordered* rule combinator to the judgment-definition DSL.
The intent is “fallback rules”: later rules should only be tried when all earlier rules fail for the
same judgment call.

This proposal is deliberately operational (like Prolog clause order + negation-as-failure), because
the current evaluator is operational: it explores multiple rules via fair interleaving.

### Surface syntax

Conceptually (pseudo-syntax):

```txt
judgment $
format ...
>>
rules ...
>>
ord_rules [
  rule "1"
  rule "2"
  ...
]
```

In the Haskell DSL used in this repo, the analogous form is:

```hs
import qualified Prelude as P

judgment $
  format ...
  P.>> rules [...]
  P.>> ord_rules [...]
```

(`P.>>` is used in examples because `TypedRedex.DSL` hides Prelude’s `(>>)`.)

### Intended semantics (precise enough to implement)

Fix a judgment call `J(args)` and a current substitution/state `s`.

- **Current behavior (today)**: all rules for `J` are tried nondeterministically and their solution
  streams are merged fairly (via `interleave` on `Disj` in `src/TypedRedex/Backend/Goal.hs`).
- **With `ord_rules`**: a rule introduced by `ord_rules` is *conditionally enabled*:
  it is allowed to run only if **no earlier rule** (in the same judgment definition, after
  desugaring) can produce *any* solution for the same call `J(args)` under `s`.

This is intentionally a “first-success commits” notion:
if an earlier rule has at least one solution, later ordered rules are not allowed to contribute any
solutions (even if they could).

### Desugaring (informal, but correct)

The earlier README text `not $ prem1` is too weak in general: order should depend on whether the
*entire earlier rule* can derive the same judgment call (including head unification + all premises),
not just whether one particular premise holds.

Let `R1, R2, ..., Rn` be the rules in source order for the judgment (after concatenating multiple
`rules [...]` blocks and expanding multiple `ord_rules [...]` blocks).

Define `Goal(Ri)` as “the goal produced by translating rule `Ri` against the current caller args”
(i.e. head unification + scheduled premises + constraints + negations).

Then each ordered rule `Ri` (introduced by `ord_rules`) is desugared to:

```txt
not $ (Goal(R1) OR Goal(R2) OR ... OR Goal(R{i-1}))
<original premises/constraints/negations of Ri>
---------------------------------------------
<original conclusion/head of Ri>
```

Expanded example (when an ordered block is appended after some prefix rules):

```txt
rules     [A, B]
>>
ord_rules [C, D, E]
```

desugars (conceptually) to:

```txt
rules [
  A,
  B,
  new_C = (not $ (A or B))               ; C
  new_D = (not $ (A or B or new_C))      ; D
  new_E = (not $ (A or B or new_C or new_D)) ; E
]
```

where each `not $ (...)` is “no earlier rule has any solution for the same judgment call”.

Concrete 2-rule example (single ordered block):

rule 1:

```txt
prem1
-----
concl
```

rule 2:

```txt
prem2
-----
concl
```

`ord_rules [rule1, rule2]` means rule 2 is desugared to:

```txt
not $ (rule1 can derive concl)
prem2
-----
concl
```

and if there is a prefix `rules [...]` before the ordered block, even *rule 1* is guarded:

```txt
not $ (any earlier rule can derive concl)
prem1
-----
concl
```

### Composition laws for `>>` (builder sequencing)

These are the laws we want at the *DSL construction* level:

- `rules [1] >> rules [2]` is equivalent to `rules [1,2]` (plain concatenation).
- `rules [1] >> ord_rules [2]` is equivalent to `rules [1, new_2]` where `new_2` is rule `2` after
  ordered desugaring against the full prefix `[1]` (i.e. guarded by failure of `[1]`).

### Implementation proposals

There are two realistic ways to implement this in the current architecture.

#### Proposal A (recommended): implement ordering at Goal translation time

Key idea: keep rules as rules, but when translating a judgment call, *wrap ordered rules with a
prefix-failure guard goal*.

This avoids rewriting `RuleM` programs (which is hard because `fresh` allocates variables inside the
free monad), and it enforces the guard *before* the rule body runs (important for termination).

Minimal changes:

1) **Extend judgment metadata** to remember which rules are “ordered”.
   For example, in `src/TypedRedex/Core/RuleF.hs`, extend `JudgmentDef`/`JudgmentCall` with a tag list:

   - `judgmentRules :: [Rule name ts]` (unchanged)
   - `judgmentRuleTags :: [RuleTag]` where `RuleTag = Plain | Ordered`
   - and similarly `jcRuleTags :: [RuleTag]`

   Invariant: `length jcRules == length jcRuleTags`.

2) **Add a builder combinator** in `src/TypedRedex/DSL.hs`:

   - `ord_rules :: [Rule name ts] -> JudgmentBuilder name modes ts ()`

   It appends the rules (like `rules`) but records `Ordered` tags for them.

3) **Change the translator** (`src/TypedRedex/Backend/Engine.hs`) from:

   - `translate jc = disjGoals [translateRule args r | r <- jcRules jc]`

   to a sequential fold that carries the prefix goal:

   - Let `prefix = Failure` initially.
   - For each rule `r_i` with tag `t_i`:
     - `base = translateRule (Just args) r_i`
     - `goal_i = case t_i of`
       - `Plain   -> base`
       - `Ordered -> Conj (Neg prefix) base`
     - update `prefix = Disj prefix goal_i`
   - Finally, return `disjGoals [goal_1, ..., goal_n]` (or just `prefix` if you build it that way).

Operationally, this matches the desugaring section:
`Neg prefix` succeeds iff no earlier rule goal produces any solution.

Notes / consequences:

- **Guard placement vs head unification**: conceptually, the “not $ prefix” guard is a *premise* of the
  ordered rule, so it runs after the rule’s head unifies with the caller, but before any other
  premises. The simple `Conj (Neg prefix) base` runs the guard even when the rule head would fail to
  match; that is equivalent for the solution set, but it can be extra work. If this matters, split
  `translateRule` into `(headGoal, restGoal)` and insert `Neg prefix` between them.
- **Termination behavior is “Prolog-like”**: if an earlier rule diverges (never produces a solution
  and never finitely fails), later ordered rules are never tried.
- **Performance**: the `Neg prefix` check *re-runs* earlier rules (as a “can any earlier rule succeed?”
  query). In the common “fallback at the end” use case, this is usually acceptable; but it is a real
  cost. (See Proposal B for an optimization path.)

4) **Trace / Typeset / MCheck**:
   - `Trace` currently selects the first successful rule left-to-right anyway, so it will usually
     *appear* consistent. If we want exact consistency with `eval`’s solution set, we should also
     add the same `Neg prefix` guard check in `searchJudgmentCall` for ordered rules.
   - `Typeset` and `MCheck` should be taught to display ordered rules distinctly (e.g. annotate rule
     labels with `[ordered]` or print an “ordered block” header), since the ordering is no longer
     visible if we only store tags.

#### Proposal B (optimization): add a committed-choice Goal constructor

If Proposal A is too slow (because each ordered rule checks `Neg prefix` and thus repeatedly
evaluates the prefix), add a new Goal constructor:

```hs
data Goal
  = ...
  | OrElse Goal Goal   -- run left; if it has any solution, commit to it; otherwise run right
```

and in `exec`:

```hs
exec (OrElse g1 g2) s =
  case exec g1 s of
    []     -> exec g2 s
    rs@(_:_) -> rs
```

Then translate an ordered block `[r1, r2, ..., rn]` as:

```txt
OrElse (Goal(r1)) (OrElse (Goal(r2)) (... Goal(rn)))
```

and if there is a plain prefix `P` before the ordered block, you can do:

```txt
OrElse (Goal(P-as-disjunction)) (Goal(ordered-block))
```

This avoids re-running the prefix for every ordered rule and matches the intended “first-success
commits” semantics more directly. It is more invasive (Goal/exec/Trace support), but it is the
cleanest operational model.

### Caveats (documented behavior, not bugs)

- **Negation-as-failure**: “not $ ...” is *existence-of-solution* under the current operational
  interpreter, not logical negation. This is acceptable here because `ord_rules` is explicitly an
  operational feature.
- **Loss of completeness**: ordered rules intentionally discard solutions from later rules whenever an
  earlier rule has any solution.
- **Non-termination**: earlier divergence prevents later ordered rules from running (consistent with
  “ordered fallback” semantics).

## Debug Interpreter

My prompt
```
   collect information during the process, when terminate, it will return a string, we can print this string

  what debug interpreter does:

  it will print information in the terminal on the fly with nice rendered information, which will make user to know where the issue is even it does not terminate.

  --- Example ---

  let's use a simple STLC typing as example, it has some rules: Ty-Int, Ty-Lam, Ty-App, Ty-Var


  suppose we want to type-check ((\y:Int (\x:Int. x)) 1) 1

  the infer is (Env, Term, Type) and the mode is (I, I, O)

  when run debug interpreter: it will show the information in the terminal:

  Matching Ty-Int --- Failed

  {then it [becomes]}

  Matching Ty-Lam --- Failed

  {then it [becomes]}

  Matching Ty-App -- Succeed

    Matching Task (1): ((\y:Int (\x:Int. x)) 1) : Int -> ?
    ....

    Matching Task (2): 1 : Int


  note the information of Int is based on the partial substitution (when we colelct some info, we can first ground this info for display)

  My given output is a bit vague and perhaps not very correct, and I cannot present certain animtation, but I described what I said.

  You have certain freedom to design this debug interpreter, and the point is to let user aware of the current processing messages,

  one of the princples is you should not expose the unification variables like (x_35, y_45) to user, use "?" for information that do not know, use ground values for those info
  we know.

  You should run it and test it by yourself, use LCTI example as a sample to test, since there're plenty of existing examples there.
```
