 Proposal Options

  Option 1: Use relation2 directly (simplest, already works)

  Since Haskell is lazy, you can reference natLt directly:

  natLt :: (Redex rel) => L Nat rel -> L Nat rel -> Relation rel
  natLt = rules2 "natLt" [natLtZero, natLtSucc]
    where
      natLtZero n m = fresh $ \m' -> do
        n <=> zro
        m <=> suc m'

      natLtSucc n m = fresh2 $ \n' m' -> do
        n <=> suc n'
        m <=> suc m'
        call $ natLt n' m'   -- Direct recursive reference works!

  The downside: you lose the "conclusion as pattern" syntax, using explicit unifications instead.

  Option 2: Tuple-based conclusion (cleaner pattern syntax)

  Add a conclude combinator:

  conclude2 :: (Redex rel, LogicType a, LogicType b)
            => (L a rel, L b rel) -> L a rel -> L b rel -> rel ()
  conclude2 (px, py) x y = x <=> px >> y <=> py

  -- Usage:
  natLtZero n m = fresh $ \m' ->
    conclude2 (zro, suc m') n m

  Or with a dedicated combinator that threads the args:

  ruleOf2 :: (Redex rel, LogicType a, LogicType b)
          => String
          -> (L a rel -> L b rel -> (L a rel, L b rel) -> rel ())
          -> L a rel -> L b rel -> Relation rel
  ruleOf2 name body = relation2 name $ \x y ->
    let concl (px, py) = x <=> px >> y <=> py
    in body x y concl

  Then:
  natLtZero = ruleOf2 "natLt-Zero" $ \_ _ concl ->
    fresh $ \m' -> concl (zro, suc m')

  Option 3: Use ImplicitParams (closest to your desired syntax)

  {-# LANGUAGE ImplicitParams #-}

  type Concl2 rel a b = (L a rel, L b rel) -> rel ()

  rule2' :: (Redex rel, LogicType a, LogicType b)
         => String
         -> ((?concl :: Concl2 rel a b) => rel ())
         -> L a rel -> L b rel -> Relation rel
  rule2' name body = relation2 name $ \x y ->
    let ?concl = \(px, py) -> x <=> px >> y <=> py
    in body

  -- Usage:
  natLtZero = rule2' "natLt-Zero" $
    fresh $ \m' -> ?concl (zro, suc m')

  Option 4: Store arguments in Relation (most invasive)

  Modify Relation to expose its arguments, then concl $ natLt x y can extract them. This requires changing the core types.

  ---
  My recommendation: Option 1 is simplest and already works. If you want pattern-like syntax, Option 2 with tuples is clean:

  natLt = rules2 "natLt" [natLtZero, natLtSucc]
    where
      natLtZero n m = fresh $ \m' ->
        conclude (zro, suc m') n m

      natLtSucc n m = fresh2 $ \n' m' -> do
        conclude (suc n', suc m') n m
        prem $ natLt n' m'

  Would you like me to implement one of these options?

> /rename
  ⎿  Please provide a name for the session. Usage: /rename <name>

> /rename reduce syntax noise
  ⎿  Session renamed to: reduce syntax noise

> I don't care about simple or diffcult or invasive or not. I only care about the syntax to be clean, since I'm designing a DSL for non-expert to use.
So please expand your proposal of Option 4 and suggest others.

⏺ Let me think about the cleanest possible syntax and work backwards to implementation.

  Target Syntax (Cleanest)

  natLt :: (Redex rel) => L Nat rel -> L Nat rel -> Relation rel
  natLt = define "natLt"
    [ rule "natLt-Zero" $ fresh $ \m' ->
        concl $ natLt zro (suc m')

    , rule "natLt-Succ" $ fresh2 $ \n' m' -> do
        concl $ natLt (suc n') (suc m')
        prem  $ natLt n' m'
    ]

  No callbacks, no explicit argument threading, just concl $ rel args....

  ---
  Option 4 Expanded: Indexed Relation Type

  Change Relation to expose its arguments:

  -- Indexed by argument types
  data Rel2 rel a b = Rel2
    { rel2Name :: String
    , rel2Arg1 :: L a rel
    , rel2Arg2 :: L b rel
    , rel2Goal :: rel ()
    }

  -- Relation application produces Rel2, exposing the args
  natLt :: L Nat rel -> L Nat rel -> Rel2 rel Nat Nat
  natLt x y = Rel2 "natLt" x y (... goal body ...)

  -- concl extracts arguments and unifies with rule's implicit args
  concl :: (?args :: (L a rel, L b rel), Redex rel)
        => Rel2 rel a b -> rel ()
  concl (Rel2 _ px py _) =
    let (x, y) = ?args in x <=> px >> y <=> py

  -- prem just runs the goal
  prem :: Rel2 rel a b -> rel ()
  prem (Rel2 _ _ _ g) = g

  -- rule2 provides the implicit args
  rule :: String -> ((?args :: (L a rel, L b rel)) => rel ()) -> ...

  ---
  Option 5: Dual-mode Relations via Type Class

  Have relations work in two modes: as goals (for prem) or as patterns (for concl):

  class RelCall f where
    type Result f
    -- For premise: execute the goal
    prem :: f -> Result f
    -- For conclusion: extract pattern args
    getPattern :: f -> PatternOf f

  data Rel2 rel a b = Rel2 (L a rel) (L b rel) (rel ())

  instance RelCall (Rel2 rel a b) where
    type Result (Rel2 rel a b) = rel ()
    prem (Rel2 _ _ g) = g
    getPattern (Rel2 x y _) = (x, y)

  -- concl uses getPattern
  concl :: (RelCall f, ?ruleArgs :: PatternOf f) => f -> rel ()
  concl r = unifyPattern ?ruleArgs (getPattern r)

  ---
  Option 6: Monadic Rule Context (ReaderT style)

  Use a dedicated monad for rule bodies that carries conclusion args:

  newtype RuleBody rel a b x = RuleBody (ReaderT (L a rel, L b rel) rel x)
    deriving (Functor, Applicative, Monad)

  -- concl in RuleBody context
  concl :: (Redex rel, LogicType a, LogicType b)
        => (L a rel -> L b rel -> Rel2 rel a b)
        -> L a rel -> L b rel
        -> RuleBody rel a b ()
  concl _ px py = RuleBody $ ReaderT $ \(x, y) ->
    x <=> px >> y <=> py

  -- define runs RuleBody with proper args
  define :: String
         -> [L a rel -> L b rel -> RuleBody rel a b ()]
         -> L a rel -> L b rel -> Relation rel
  define name rules = relation2 name $ \x y ->
    conde [runReaderT body (x, y) | body <- rules]

  Usage:
  natLt = define "natLt" [natLtZero, natLtSucc]
    where
      natLtZero _ _ = fresh $ \m' ->
        concl natLt zro (suc m')

      natLtSucc _ _ = fresh2 $ \n' m' -> do
        concl natLt (suc n') (suc m')
        prem $ natLt n' m'

  Still has _ _ noise.

  ---
  Option 7: Self-reference via mdo (RecursiveDo)

  {-# LANGUAGE RecursiveDo #-}

  natLt :: (Redex rel, MonadFix rel) => L Nat rel -> L Nat rel -> Relation rel
  natLt = mdo
    self <- define "natLt"
      [ rule "Zero" $ fresh $ \m' ->
          concl $ self zro (suc m')
      , rule "Succ" $ fresh2 $ \n' m' -> do
          concl $ self (suc n') (suc m')
          prem  $ self n' m'
      ]
    pure self

  ---
  Option 8: Overloaded concl/prem with Smart Application (Recommended)

  The cleanest approach—make relation application return a rich type:

  -- Applied relation: stores both args and goal
  data Applied2 rel a b = Applied2
    { appArgs :: (L a rel, L b rel)
    , appGoal :: rel ()
    }

  -- Type class for "callable as relation"
  class Callable2 f rel a b where
    apply2 :: f -> L a rel -> L b rel -> Applied2 rel a b

  -- concl: extract pattern, unify with rule args
  concl :: (?ruleArgs :: (L a rel, L b rel), Redex rel, LogicType a, LogicType b)
        => Applied2 rel a b -> rel ()
  concl (Applied2 (px, py) _) =
    let (x, y) = ?ruleArgs in x <=> px >> y <=> py

  -- prem: just run the goal
  prem :: Applied2 rel a b -> rel ()
  prem = appGoal

  -- Define syntax
  define2 :: (Redex rel, LogicType a, LogicType b)
          => String
          -> [(?ruleArgs :: (L a rel, L b rel)) => rel ()]
          -> L a rel -> L b rel -> Relation rel
  define2 name rules = relation2 name $ \x y ->
    let ?ruleArgs = (x, y)
    in conde rules

  Final syntax:
  natLt :: (Redex rel) => L Nat rel -> L Nat rel -> Applied2 rel Nat Nat
  natLt x y = Applied2 (x, y) (body x y)
    where body = ... -- defined via define2

  -- Or with the define2 pattern:
  natLt = define2 "natLt"
    [ fresh $ \m' -> concl $ natLt zro (suc m')

    , fresh2 $ \n' m' -> do
        concl $ natLt (suc n') (suc m')
        prem  $ natLt n' m'
    ]

  ---
  Summary

  | Option | Syntax cleanliness | Impl complexity | Notes                |
  |--------|--------------------|-----------------|----------------------|
  | 4      | ★★★★☆              | Medium          | Indexed Rel2 type    |
  | 5      | ★★★★☆              | Medium          | Type class dual-mode |
  | 6      | ★★★☆☆              | Low             | Still has _ _ args   |
  | 7      | ★★★★★              | Low             | Needs MonadFix       |
  | 8      | ★★★★★              | Medium          | Most flexible        |

  My recommendation for DSL: Option 8 or a variant of Option 4, as they give you the exact syntax you want with concl $ natLt zro (suc m').

  Want me to implement one of these?