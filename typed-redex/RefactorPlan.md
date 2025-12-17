## Plan List

Refactoring Plan

  Phase 1: Initial Module Splits (prepare for reorganization) ✅ DONE

  1.1 Split Utils/Redex.hs ✅
  - Created Utils/Fresh.hs — fresh, fresh2, ..., argument, argument2, ..., L, Var'
  - Created Utils/Relation.hs — relation, relation2, ..., call, premise, embed, (===), (<=>), conde
  - Created Utils/Run.hs — run, run2, ..., eval
  - Created Utils/Format.hs — formatCon, prettyLogic, intercalate, subscriptNum
  - Updated Utils/Redex.hs to re-export from new modules (backward compatible)
  - Updated all interpreter imports

  1.2 Extract interpreter internals ✅
  - Created Core/Internal/Unify.hs — flatteningUnify, occursCheck, evalFromRead
  - Updated SubstRedex.hs and TracingRedex.hs to import from Unify.hs

  1.3 Extract shared SubstRedex/TracingRedex code ✅
  - Created Core/Internal/SubstCore.hs — VarRepr type, displayVarInt helper
  - Both interpreters now import VarRepr from SubstCore
  - Shared substitution pattern documented (interpreters have similar structure)

  1.4 Remove deprecated Rule.hs ✅
  - All examples already use Define.hs style
  - Utils/Rule.hs removed (axiom*, rules* combinators no longer needed)

  ---
  Phase 2: Three-Layer Architecture ✅ DONE

  2.0 Reorganize into three layers ✅

  Completed structure:
    TypedRedex/
    ├── Core/Internal/       ← Kernel (dev-only)
    │   ├── Logic.hs         -- Logic, Var, Reified, LogicType
    │   ├── Redex.hs         -- Redex typeclass, (<=>), unify
    │   ├── Relation.hs      -- relation, relation2, ..., conde (solver primitives)
    │   ├── Unify.hs         -- flatteningUnify, occursCheck
    │   └── SubstCore.hs     -- shared interpreter primitives
    │
    ├── DSL/                 ← User-facing API
    │   ├── Fresh.hs         -- fresh, fresh2, ...
    │   ├── Define.hs        -- judgment, rule, concl, prem
    │   └── Type.hs          -- type-level helpers users need
    │
    ├── Interp/              ← Interpreters
    │   ├── Stream.hs        -- Stream type for backtracking search
    │   ├── Subst.hs         -- SubstRedex
    │   ├── Tracing.hs       -- TracingRedex
    │   ├── Deep.hs          -- DeepRedex
    │   ├── Run.hs           -- run, run2, ..., eval
    │   ├── Format.hs        -- prettyLogic, formatCon
    │   └── PrettyPrint.hs   -- variable naming
    │
    └── TypedRedex.hs        ← Re-export public API only (DSL + Interp)

  Principle: Users import TypedRedex and get DSL + Interp. They never see Core.Internal.*.

  ---
  Phase 3: Naming Cleanup (after architecture is stable)

  3.1 Rename core type aliases
  - L a rel → LTerm a rel
  - Var' a rel → LVar a rel
  - Update all usages

  3.2 Fix arity suffix inconsistency
  - Add judgment1 to Define.hs (or remove all *1 variants — pick one convention)
  - Ensure rule, fresh, relation, run, argument families are consistent

  3.3 Clarify call variants
  - Rename embed → callDirect
  - Remove premise alias (or keep if you prefer paper notation)
  - Document the difference clearly

  3.4 Unify operators
  - Remove (===), keep only (<=>)
  - Update all call sites to use Ground $ project value pattern

  ---
  Phase 4: Extension Reduction

  4.1 Remove ImplicitParams from Define.hs
  - Replace ?concl with explicit RuleEnv parameter or ReaderT
  - This also removes need for ImpredicativeTypes

  4.2 Clean up ApplicativeDo usage
  - Review Logic.hs and Utils files
  - Replace with explicit <*> where it improves clarity

  4.3 Replace TypeApplications with Proxy
  - In DeepRedex.hs, change varNaming @a pattern to varNaming (Proxy @a)
  - More portable, less extension-heavy

  ---
  Phase 5: Format/Pretty-Print Consolidation

  5.1 Move domain-specific formatCon cases to examples
  - Keep only generic Con name args → "name(arg1, arg2, ...)" in library
  - Each example provides its own FormatConfig or custom formatter

  5.2 Unify pretty-printing
  - Consolidate prettyLogic (Utils), prettyL/prettyReified (DeepRedex), prettyResolved (TracingRedex)
  - Create single parametric pretty-printer taking a variable lookup function

  ---
  Phase 6: Optional Cleanup

  6.1 Consider simplifying Applied family
  - Evaluate GADT with type-level list vs current Applied/Applied2/...
  - May not be worth the complexity — decide after other refactors

  6.2 Optional: Rename Logic.hs types
  - Logic a var → Term a var (if desired)
  - Or rename module to TypedRedex.Core.Internal.Term

  ---
  Session Order

  | Session | Task                                   | Description                              | Status |
  |---------|----------------------------------------|------------------------------------------|--------|
  | 1       | 1.1 Split Utils/Redex.hs               | Split into focused modules               | ✅     |
  | 2       | 1.2 Extract Unify.hs                   | Move interpreter helpers to Internal     | ✅     |
  | 3       | 1.3 Extract SubstCore.hs               | Deduplicate SubstRedex/TracingRedex      | ✅     |
  | 4       | 1.4 Deprecate Rule.hs                  | Migrate to Define.hs style               | ✅     |
  | 5       | 2.0 Three-layer reorganization         | Core/Internal, DSL, Interp structure     | ✅     |
  | 6       | 3.1 Rename L/Var'                      | LTerm, LVar                              |        |
  | 7       | 3.2 Fix arity suffixes                 | Consistent *1 convention                 |        |
  | 8       | 3.3 + 3.4 Call variants + operators    | callDirect, remove (===)                 |        |
  | 9       | 4.1 Remove ImplicitParams              | Explicit RuleEnv or ReaderT              |        |
  | 10      | 4.2 + 4.3 Extension cleanup            | ApplicativeDo, TypeApplications          |        |
  | 11      | 5.1 + 5.2 Format consolidation         | Unified pretty-printing                  |        |
  | 12      | 6.1 + 6.2 Optional cleanup             | Applied family, Logic rename             |        |
