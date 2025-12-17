
⏺ Interesting question! Let me brainstorm some search strategy modifications that could support premises-first syntax:

  Approach 1: Free Monad / Deferred Execution

  Instead of executing concl and prem immediately, collect them as data, then reorder:

  -- Rule body collects operations as data
  data RuleF rel next where
    Concl :: Applied rel pat -> next -> RuleF rel next
    Prem  :: rel () -> next -> RuleF rel next
    Done  :: RuleF rel next

  type RuleM rel = Free (RuleF rel)

  -- After body finishes, we have a data structure:
  --   [Prem (natEq n' m'), Concl (natEq (suc n') (suc m'))]
  --
  -- Then interpret with correct ordering:
  --   1. Find the Concl, unify it
  --   2. Execute all Prems

  Pros: Syntax stays clean (premises-first works)
  Cons: Extra machinery, rule body is in a different monad than rel

  ---
  Approach 2: Constraint-Based / Residuation

  Instead of immediately enumerating unbound variables, suspend goals until variables become bound:

  -- When natEq n' m' is called with unbound n', m':
  -- Instead of: enumerate all (n, m) pairs → infinite!
  -- Do: suspend the goal, create constraint "when n' or m' gets bound, wake me up"

  -- Later when concl unifies: n' <=> suc n'', m' <=> suc m''
  -- The suspended goal wakes up with more constraints

  This is essentially CLP (Constraint Logic Programming). Goals with insufficient bindings become constraints that wait.

  Pros: Most elegant, handles complex cases
  Cons: Requires significant changes to the core solver

  ---
  Approach 3: Goal Reordering with Dependency Analysis

  Analyze which variables each goal needs vs. provides, then topologically sort:

  -- prem $ natEq n' m'                → needs: n', m'  provides: (if they unify)
  -- concl $ natEq (suc n') (suc m')   → provides: n', m' (from input unification)

  -- Dependency: prem needs n',m' which concl provides
  -- Automatic reorder: run concl first, then prem

  Pros: Works automatically, no syntax change
  Cons: Complex to implement, may not handle all cases

  ---
  Approach 4: Two-Pass with Explicit Structure

  Separate "declare conclusion" from "run premises":

  -- New syntax using a record
  natEqSucc = rule2 "eq-succ" $ fresh2 $ \n' m' -> Rule
    { conclusion = natEq (suc n') (suc m')
    , premises   = [prem $ natEq n' m']
    }

  The judgment function then:
  1. Unifies conclusion
  2. Runs premises in sequence

  Pros: Clear semantics, easy to implement
  Cons: More verbose syntax

  ---
  My Recommendation: Approach 1 (Free Monad)

  It keeps the clean do-notation syntax while fixing the semantics:

  -- User writes (looks identical!):
  natEqSucc = rule2 "eq-succ" $ fresh2 $ \n' m' -> do
    prem $ natEq n' m'
    concl $ natEq (suc n') (suc m')

  -- Under the hood, RuleM collects operations as data
  -- judgment2 interprets them in correct order

  Should I implement the Free Monad approach?
