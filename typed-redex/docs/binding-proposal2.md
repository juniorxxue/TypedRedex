

• Option 2A in TypedRedex is: free vars are explicit “atoms” (TmVar/TyVar) used in Var nodes and in Ctx keys; binders store bodies in a scoped form
  where the bound var is an internal index. “Opening” a binder = pick a fresh atom and instantiate.

  Here’s a concrete sketch in TypedRedex style.

  ———

  ## 1) Two namespaces: TmVar and TyVar

  Make them ground tokens (not logic vars) so “fresh” is just “new unique id”, no diseq constraints needed.

  data TmVar = X Nat   deriving (Eq, Show)  -- or Int; Nat keeps LogicType easy
  data TyVar = A Nat   deriving (Eq, Show)

  -- You’ll want a primitive in the Redex monad:
  class Redex rel => RedexNames rel where
    freshTmVar :: rel TmVar
    freshTyVar :: rel TyVar

  tmvG :: (RedexNames rel) => rel (LTerm TmVar rel)
  tmvG = Ground . project <$> freshTmVar

  tyvG :: (RedexNames rel) => rel (LTerm TyVar rel)
  tyvG = Ground . project <$> freshTyVar

  Key point: these are object-language names (ground), separate from TypedRedex unification vars.

  ———

  ## 2) Name-keyed environments/contexts

  Use an association-list context keyed by the name types.

  STLC-ish (only term vars):

  data Ctx = Empty | BindTm TmVar Ty Ctx

  System F-ish (both namespaces):

  data Ctx
    = Empty
    | BindTm TmVar Ty Ctx
    | BindTy TyVar Ctx

  Lookup becomes a pure relational “enumerate bindings” relation (no diseq needed if you maintain “fresh keys only”):

  lookupTm :: Redex rel => Judge rel '[Ctx, TmVar, Ty]
  lookupTm = judgment "lookupTm" [here, there]
    where
      here = rule "lookupTm-here" $ fresh3 $ \x a g ->
        concl $ lookupTm (bindTm x a g) x a

      there = rule "lookupTm-there" $ fresh5 $ \x a g y b -> do
        concl $ lookupTm (bindTm x a g) y b
        prem  $ lookupTm g y b

  If you always extend contexts with freshTmVar/freshTyVar, keys are unique so querying lookupTm Γ x ? stays deterministic.

  ———

  ## 3) Binders and “open” in a Judge

  You need a binder container that hides indices. Think “Scope1 for one bound variable”, in the spirit of bound’s Scope.

  For terms (λ binds a term var):

  data Tm
    = Var TmVar
    | Lam Ty (BindTm Tm)     -- binder, no user-visible index
    | App Tm Tm
    deriving (Eq, Show)

  -- BindTm is an abstract locally-nameless scope:
  data BindTm t  -- don’t export constructors
  openTm1  :: Redex rel => Judge rel '[BindTm Tm, TmVar, Tm]   -- open with a name
  closeTm1 :: Redex rel => Judge rel '[TmVar, Tm, BindTm Tm]   -- close over a name
  instTm1  :: Redex rel => Judge rel '[BindTm Tm, Tm, Tm]      -- instantiate with a term (β-subst)

  ### Typing rule (this is the “open binder step”)

  Example: STLC typeof for annotated lambdas, using openTm1:

  typeof :: Redex rel => Judge rel '[Ctx, Tm, Ty]
  typeof = judgment "typeof" [typeofVar, typeofLam, typeofApp]
    where
      typeofVar = rule "typeof-var" $ fresh3 $ \g x a -> do
        concl $ typeof g (var x) a
        prem  $ lookupTm g x a

      typeofLam = rule "typeof-lam" $ fresh4 $ \g a bnd b -> do
        concl $ typeof g (lam a bnd) (tarr a b)

        x <- tmvG           -- fresh *ground* name token
        body <- fresh $ \body -> do
          prem $ openTm1 bnd x body
          pure body

        prem $ typeof (bindTm x a g) body b

      typeofApp = ...

  Notes:

  - x <- tmvG is the “fresh name” step.
  - openTm1 bnd x body is the locally-nameless “open”.
  - No de Bruijn, no shifting in user code.

  ### β-reduction / substitution becomes “instantiate binder”

  Instead of subst0 + shifts, you do:

  stepBeta = rule "β" $ fresh3 $ \bnd v out -> do
    concl $ step (app (lam a bnd) v) out
    prem  $ value v
    prem  $ instTm1 bnd v out

  That’s the big ergonomic payoff of 2A.

  ———

  ## 4) Extending to System F (two namespaces)

  You add two “open/instantiate” families:

  - type-binder in types: openTy1 :: BindTy Ty -> TyVar -> Ty
  - type-binder in terms (Λ binds type vars in term): openTyInTm1 :: BindTyInTm Tm -> TyVar -> Tm
  - and type-substitution: instTy1 :: BindTy Ty -> Ty -> Ty etc.

  Then ∀ elimination / type application is just “instantiate type binder with a type”, again no shifting.

  ———

  If you want, I can sketch the minimal internal representation for BindTm/BindTy that makes openTm1/instTm1 definable once (and keeps it LogicType-
  friendly for unification and pretty-printing).


› x <- tmvG           -- fresh *ground* name token
          body <- fresh $ \body -> do
            prem $ openTm1 bnd x body
            pure body

  this DSL is ugly and confuse users, suggest better dsls


────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────

• You’re right: exposing the “plumbing” (fresh + prem open…) is gross. In Option 2A you can hide it behind small combinators and keep the rule
  bodies close to paper.

  DSL 1: unbind / lunbind (Unbound-style)
  Provide a helper that chooses a fresh object-name and opens the binder, returning both:

  unbindTm1
    :: (Redex rel, RedexNames rel)
    => LTerm (BindTm Tm) rel
    -> rel (LTerm TmVar rel, LTerm Tm rel)

  Usage:

  typeofLam = rule "typeof-lam" $ fresh4 $ \g a bnd b -> do
    concl $ typeof g (lam a bnd) (tarr a b)
    (x, body) <- unbindTm1 bnd
    prem $ typeof (bindTm x a g) body b

  (Implement unbindTm1 once using freshTmVar + fresh + prem (openTm1 …) internally.)

  DSL 2: “let-premise” helpers (exists / exists2)
  A tiny generic combinator removes the “allocate output var then premise then return it” pattern:

  exists  :: (Redex rel, LogicType a) => (LTerm a rel -> rel ()) -> rel (LTerm a rel)
  exists2 :: (Redex rel, LogicType a, LogicType b) => (LTerm a rel -> LTerm b rel -> rel ()) -> rel (LTerm a rel, LTerm b rel)

  DSL 3: Domain-specific “under binder” combinators
  Most rules don’t care about the chosen name at all; they just want the extended context + opened body:
    :: (Redex rel, RedexNames rel)
    => LTerm Ctx rel -> LTerm Ty rel -> LTerm (BindTm Tm) rel
    -> (LTerm Ctx rel -> LTerm Tm rel -> rel a)
    -> rel a

  Usage:

  typeofLam = rule "typeof-lam" $ fresh4 $ \g a bnd b -> do
    concl $ typeof g (lam a bnd) (tarr a b)
    underLam g a bnd $ \g' body ->
      prem $ typeof g' body b

  If you want, I can propose the exact API surface for TypedRedex.DSL.Bind (names + unbind/instantiate + underLam/underForall) so it stays uniform
  across term/type binders.
