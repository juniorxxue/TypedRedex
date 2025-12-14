{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Main (main) where

import Control.Applicative (empty)
import Shallow.Core.Kanren
import Shallow.Core.Internal.Logic (Logic (Ground), LogicType (..))
import Shallow.Interpreters.SubstKanren (runSubstKanren, takeS, Stream)
import Shallow.Utils.Type (quote0, quote1, quote2)

-- System F Type Checking
-- Uses de Bruijn indices for both term and type variables
--
-- Types:
--   τ ::= Unit | α | τ₁ → τ₂ | ∀α. τ
--
-- Terms:
--   e ::= () | x | λx:τ. e | e₁ e₂ | Λα. e | e [τ]
--
-- Typing rules:
--   Γ(x) = A              Γ ⊢ () : Unit
--   ─────────────
--   Γ ⊢ x : A
--
--   Γ, x:A ⊢ e : B        Γ ⊢ e₁ : A → B    Γ ⊢ e₂ : A
--   ───────────────────   ─────────────────────────────
--   Γ ⊢ λx:A. e : A → B   Γ ⊢ e₁ e₂ : B
--
--   Γ, α ⊢ e : A          Γ ⊢ e : ∀α. A
--   ─────────────────     ───────────────────
--   Γ ⊢ Λα. e : ∀α. A     Γ ⊢ e [B] : A[α:=B]

-- Natural numbers for de Bruijn indices
data Nat = Z | S Nat deriving (Eq, Show)

instance LogicType Nat where
  data Reified Nat var = ZR | SR (Logic Nat var)

  project Z = ZR
  project (S n) = SR (Ground $ project n)

  reify ZR = Just Z
  reify (SR (Ground n)) = S <$> reify n
  reify _ = Nothing

  quote ZR = quote0 "Z" ZR
  quote (SR n) = quote1 "S" SR n

  unifyVal _ ZR ZR = pure ()
  unifyVal unif (SR x) (SR y) = unif x y
  unifyVal _ _ _ = empty

  derefVal _ ZR = pure Z
  derefVal deref (SR n) = S <$> deref n

zro :: Logic Nat var
zro = Ground ZR

suc :: Logic Nat var -> Logic Nat var
suc = Ground . SR

-- Nat equality check
natEq :: (Kanren rel) => L Nat rel -> L Nat rel -> Relation rel
natEq = relation2 "natEq" $ \n m ->
  conde
    [ do
        n <=> zro
        m <=> zro
        pure ()
    , fresh2 $ \n' m' -> do
        n <=> suc n'
        m <=> suc m'
        call $ natEq n' m'
        pure ()
    ]

-- Less than check (strict)
natLt :: (Kanren rel) => L Nat rel -> L Nat rel -> Relation rel
natLt = relation2 "natLt" $ \n m ->
  conde
    [ -- 0 < S m'
      fresh $ \m' -> do
        n <=> zro
        m <=> suc m'
        pure ()
    , -- S n' < S m'  iff  n' < m'
      fresh2 $ \n' m' -> do
        n <=> suc n'
        m <=> suc m'
        call $ natLt n' m'
        pure ()
    ]

-- Types
data Ty
  = TUnit        -- Unit type
  | TVar Nat     -- Type variable (de Bruijn index)
  | TArr Ty Ty   -- Function type: A → B
  | TAll Ty      -- Universal type: ∀α. A (binding increments indices)
  deriving (Eq, Show)

instance LogicType Ty where
  data Reified Ty var
    = TUnitR
    | TVarR (Logic Nat var)
    | TArrR (Logic Ty var) (Logic Ty var)
    | TAllR (Logic Ty var)

  project TUnit = TUnitR
  project (TVar n) = TVarR (Ground $ project n)
  project (TArr a b) = TArrR (Ground $ project a) (Ground $ project b)
  project (TAll ty) = TAllR (Ground $ project ty)

  reify TUnitR = Just TUnit
  reify (TVarR (Ground n)) = TVar <$> reify n
  reify (TArrR (Ground a) (Ground b)) = TArr <$> reify a <*> reify b
  reify (TAllR (Ground ty)) = TAll <$> reify ty
  reify _ = Nothing

  quote TUnitR = quote0 "TUnit" TUnitR
  quote (TVarR n) = quote1 "TVar" TVarR n
  quote (TArrR a b) = quote2 "TArr" TArrR a b
  quote (TAllR ty) = quote1 "TAll" TAllR ty

  unifyVal _ TUnitR TUnitR = pure ()
  unifyVal unif (TVarR n) (TVarR n') = unif n n'
  unifyVal unif (TArrR a b) (TArrR a' b') = unif a a' *> unif b b'
  unifyVal unif (TAllR ty) (TAllR ty') = unif ty ty'
  unifyVal _ _ _ = empty

  derefVal _ TUnitR = pure TUnit
  derefVal deref (TVarR n) = TVar <$> deref n
  derefVal deref (TArrR a b) = TArr <$> deref a <*> deref b
  derefVal deref (TAllR ty) = TAll <$> deref ty

tunit :: Logic Ty var
tunit = Ground TUnitR

tvar :: Logic Nat var -> Logic Ty var
tvar = Ground . TVarR

tarr :: Logic Ty var -> Logic Ty var -> Logic Ty var
tarr a b = Ground $ TArrR a b

tall :: Logic Ty var -> Logic Ty var
tall = Ground . TAllR

-- Terms
data Tm
  = Unit          -- Unit value: ()
  | Var Nat       -- Term variable (de Bruijn index)
  | Lam Ty Tm     -- Term abstraction: λx:A. e
  | App Tm Tm     -- Term application: e₁ e₂
  | TLam Tm       -- Type abstraction: Λα. e
  | TApp Tm Ty    -- Type application: e [A]
  deriving (Eq, Show)

instance LogicType Tm where
  data Reified Tm var
    = UnitR
    | VarR (Logic Nat var)
    | LamR (Logic Ty var) (Logic Tm var)
    | AppR (Logic Tm var) (Logic Tm var)
    | TLamR (Logic Tm var)
    | TAppR (Logic Tm var) (Logic Ty var)

  project Unit = UnitR
  project (Var n) = VarR (Ground $ project n)
  project (Lam ty b) = LamR (Ground $ project ty) (Ground $ project b)
  project (App f a) = AppR (Ground $ project f) (Ground $ project a)
  project (TLam b) = TLamR (Ground $ project b)
  project (TApp e ty) = TAppR (Ground $ project e) (Ground $ project ty)

  reify UnitR = Just Unit
  reify (VarR (Ground n)) = Var <$> reify n
  reify (LamR (Ground ty) (Ground b)) = Lam <$> reify ty <*> reify b
  reify (AppR (Ground f) (Ground a)) = App <$> reify f <*> reify a
  reify (TLamR (Ground b)) = TLam <$> reify b
  reify (TAppR (Ground e) (Ground ty)) = TApp <$> reify e <*> reify ty
  reify _ = Nothing

  quote UnitR = quote0 "Unit" UnitR
  quote (VarR n) = quote1 "Var" VarR n
  quote (LamR ty b) = quote2 "Lam" LamR ty b
  quote (AppR f a) = quote2 "App" AppR f a
  quote (TLamR b) = quote1 "TLam" TLamR b
  quote (TAppR e ty) = quote2 "TApp" TAppR e ty

  unifyVal _ UnitR UnitR = pure ()
  unifyVal unif (VarR n) (VarR n') = unif n n'
  unifyVal unif (LamR ty b) (LamR ty' b') = unif ty ty' *> unif b b'
  unifyVal unif (AppR f a) (AppR f' a') = unif f f' *> unif a a'
  unifyVal unif (TLamR b) (TLamR b') = unif b b'
  unifyVal unif (TAppR e ty) (TAppR e' ty') = unif e e' *> unif ty ty'
  unifyVal _ _ _ = empty

  derefVal _ UnitR = pure Unit
  derefVal deref (VarR n) = Var <$> deref n
  derefVal deref (LamR ty b) = Lam <$> deref ty <*> deref b
  derefVal deref (AppR f a) = App <$> deref f <*> deref a
  derefVal deref (TLamR b) = TLam <$> deref b
  derefVal deref (TAppR e ty) = TApp <$> deref e <*> deref ty

unit' :: Logic Tm var
unit' = Ground UnitR

var :: Logic Nat var -> Logic Tm var
var = Ground . VarR

lam :: Logic Ty var -> Logic Tm var -> Logic Tm var
lam ty b = Ground $ LamR ty b

app :: Logic Tm var -> Logic Tm var -> Logic Tm var
app f a = Ground $ AppR f a

tlam :: Logic Tm var -> Logic Tm var
tlam = Ground . TLamR

tapp :: Logic Tm var -> Logic Ty var -> Logic Tm var
tapp e ty = Ground $ TAppR e ty

-- Typing context: tracks both term and type bindings
-- Term bindings: actual types
-- Type bindings: just markers (type variables are represented by de Bruijn indices)
data Ctx
  = Nil
  | TmBind Ty Ctx   -- Term variable binding: x : A
  | TyBind Ctx      -- Type variable binding: α (marker for ∀ elimination)
  deriving (Eq, Show)

instance LogicType Ctx where
  data Reified Ctx var
    = NilR
    | TmBindR (Logic Ty var) (Logic Ctx var)
    | TyBindR (Logic Ctx var)

  project Nil = NilR
  project (TmBind ty ctx) = TmBindR (Ground $ project ty) (Ground $ project ctx)
  project (TyBind ctx) = TyBindR (Ground $ project ctx)

  reify NilR = Just Nil
  reify (TmBindR (Ground ty) (Ground ctx)) = TmBind <$> reify ty <*> reify ctx
  reify (TyBindR (Ground ctx)) = TyBind <$> reify ctx
  reify _ = Nothing

  quote NilR = quote0 "Nil" NilR
  quote (TmBindR ty ctx) = quote2 "TmBind" TmBindR ty ctx
  quote (TyBindR ctx) = quote1 "TyBind" TyBindR ctx

  unifyVal _ NilR NilR = pure ()
  unifyVal unif (TmBindR ty ctx) (TmBindR ty' ctx') = unif ty ty' *> unif ctx ctx'
  unifyVal unif (TyBindR ctx) (TyBindR ctx') = unif ctx ctx'
  unifyVal _ _ _ = empty

  derefVal _ NilR = pure Nil
  derefVal deref (TmBindR ty ctx) = TmBind <$> deref ty <*> deref ctx
  derefVal deref (TyBindR ctx) = TyBind <$> deref ctx

nil :: Logic Ctx var
nil = Ground NilR

tmBind :: Logic Ty var -> Logic Ctx var -> Logic Ctx var
tmBind ty ctx = Ground $ TmBindR ty ctx

tyBind :: Logic Ctx var -> Logic Ctx var
tyBind = Ground . TyBindR

-- Term variable lookup: lookupTm ctx n ty
-- Looks up term variable at de Bruijn index n, skipping type bindings
lookupTm :: (Kanren rel) => L Ctx rel -> L Nat rel -> L Ty rel -> Relation rel
lookupTm = relation3 "lookupTm" $ \ctx n ty ->
  conde
    [ -- Found at index 0
      fresh $ \rest -> do
        n <=> zro
        ctx <=> tmBind ty rest
        pure ()
    , -- Decrement index, continue through term binding
      fresh3 $ \ty' rest n' -> do
        n <=> suc n'
        ctx <=> tmBind ty' rest
        call $ lookupTm rest n' ty
        pure ()
    , -- Skip type binding (doesn't affect term indices)
      fresh $ \rest -> do
        ctx <=> tyBind rest
        call $ lookupTm rest n ty
        pure ()
    ]

-- Count type bindings in context (used to determine current type depth)
countTyBinds :: (Kanren rel) => L Ctx rel -> L Nat rel -> Relation rel
countTyBinds = relation2 "countTyBinds" $ \ctx n ->
  conde
    [ do
        ctx <=> nil
        n <=> zro
        pure ()
    , fresh2 $ \ty rest -> do
        ctx <=> tmBind ty rest
        call $ countTyBinds rest n
        pure ()
    , fresh2 $ \rest n' -> do
        ctx <=> tyBind rest
        n <=> suc n'
        call $ countTyBinds rest n'
        pure ()
    ]

-- Type substitution: substTy depth subTy ty result
-- Substitutes type variable at index 'depth' with 'subTy' in 'ty'
-- Handles de Bruijn index shifting
substTy :: (Kanren rel) => L Nat rel -> L Ty rel -> L Ty rel -> L Ty rel -> Relation rel
substTy = relation4 "substTy" $ \depth subTy ty result ->
  conde
    [ -- Unit stays Unit
      do
        ty <=> tunit
        result <=> tunit
        pure ()
    , -- Variable: check if it's the one to substitute
      fresh $ \n -> do
        ty <=> tvar n
        call $ substTyVar depth subTy n result
        pure ()
    , -- Arrow: substitute in both components
      fresh4 $ \a b a' b' -> do
        ty <=> tarr a b
        call $ substTy depth subTy a a'
        call $ substTy depth subTy b b'
        result <=> tarr a' b'
        pure ()
    , -- Forall: increment depth, substitute in body
      fresh3 $ \body body' depth' -> do
        ty <=> tall body
        depth' <=> suc depth
        call $ substTy depth' subTy body body'
        result <=> tall body'
        pure ()
    ]

-- Helper for substituting type variable
-- If var == depth, substitute; if var > depth, decrement; otherwise keep
substTyVar :: (Kanren rel) => L Nat rel -> L Ty rel -> L Nat rel -> L Ty rel -> Relation rel
substTyVar = relation4 "substTyVar" $ \depth subTy n result ->
  conde
    [ -- n == depth: substitute
      do
        call $ natEq n depth
        result <=> subTy
        pure ()
    , -- n < depth: free variable, keep unchanged
      do
        call $ natLt n depth
        result <=> tvar n
        pure ()
    , -- n > depth: bound variable from outer scope, decrement
      fresh $ \n' -> do
        call $ natLt depth n
        n <=> suc n'
        result <=> tvar n'
        pure ()
    ]

-- Shift type variables: shiftTy cutoff amount ty result
-- Increments free variables (>= cutoff) by 'amount'
shiftTy :: (Kanren rel) => L Nat rel -> L Nat rel -> L Ty rel -> L Ty rel -> Relation rel
shiftTy = relation4 "shiftTy" $ \cutoff amount ty result ->
  conde
    [ -- Unit
      do
        ty <=> tunit
        result <=> tunit
        pure ()
    , -- Variable: shift if >= cutoff
      fresh $ \n -> do
        ty <=> tvar n
        call $ shiftTyVar cutoff amount n result
        pure ()
    , -- Arrow
      fresh4 $ \a b a' b' -> do
        ty <=> tarr a b
        call $ shiftTy cutoff amount a a'
        call $ shiftTy cutoff amount b b'
        result <=> tarr a' b'
        pure ()
    , -- Forall: increment cutoff
      fresh3 $ \body body' cutoff' -> do
        ty <=> tall body
        cutoff' <=> suc cutoff
        call $ shiftTy cutoff' amount body body'
        result <=> tall body'
        pure ()
    ]

-- Addition for shifting
addNat :: (Kanren rel) => L Nat rel -> L Nat rel -> L Nat rel -> Relation rel
addNat = relation3 "addNat" $ \n m sum' ->
  conde
    [ do
        n <=> zro
        sum' <=> m
        pure ()
    , fresh2 $ \n' sum'' -> do
        n <=> suc n'
        sum' <=> suc sum''
        call $ addNat n' m sum''
        pure ()
    ]

shiftTyVar :: (Kanren rel) => L Nat rel -> L Nat rel -> L Nat rel -> L Ty rel -> Relation rel
shiftTyVar = relation4 "shiftTyVar" $ \cutoff amount n result ->
  conde
    [ -- n < cutoff: bound variable, keep
      do
        call $ natLt n cutoff
        result <=> tvar n
        pure ()
    , -- n >= cutoff: free variable, shift
      fresh $ \n' -> do
        -- n >= cutoff means not (n < cutoff)
        -- We check by: either n == cutoff or n > cutoff
        conde
          [ call $ natEq n cutoff
          , call $ natLt cutoff n
          ]
        call $ addNat n amount n'
        result <=> tvar n'
        pure ()
    ]

-- Type checking: typeof ctx e ty
-- Γ ⊢ e : A
typeof :: (Kanren rel) => L Ctx rel -> L Tm rel -> L Ty rel -> Relation rel
typeof = relation3 "typeof" $ \ctx e ty ->
  conde
    [ -- Unit: Γ ⊢ () : Unit
      do
        e <=> unit'
        ty <=> tunit
        pure ()
    , -- Var: Γ(x) = A ⟹ Γ ⊢ x : A
      fresh $ \n -> do
        e <=> var n
        call $ lookupTm ctx n ty
        pure ()
    , -- Lam: Γ, x:A ⊢ e : B ⟹ Γ ⊢ λx:A.e : A → B
      fresh3 $ \tyA body tyB -> do
        e <=> lam tyA body
        ty <=> tarr tyA tyB
        call $ typeof (tmBind tyA ctx) body tyB
        pure ()
    , -- App: Γ ⊢ e₁ : A → B, Γ ⊢ e₂ : A ⟹ Γ ⊢ e₁ e₂ : B
      fresh3 $ \e1 e2 tyA -> do
        e <=> app e1 e2
        call $ typeof ctx e1 (tarr tyA ty)
        call $ typeof ctx e2 tyA
        pure ()
    , -- TLam: Γ, α ⊢ e : A ⟹ Γ ⊢ Λα.e : ∀α.A
      fresh2 $ \body tyA -> do
        e <=> tlam body
        ty <=> tall tyA
        call $ typeof (tyBind ctx) body tyA
        pure ()
    , -- TApp: Γ ⊢ e : ∀α.A ⟹ Γ ⊢ e [B] : A[α:=B]
      -- Note: We substitute at depth 0 (the outermost binding)
      fresh4 $ \e' tyB tyA tyA' -> do
        e <=> tapp e' tyB
        call $ typeof ctx e' (tall tyA)
        call $ substTy zro tyB tyA tyA'
        ty <=> tyA'
        pure ()
    ]

-- Run type checking in mode (I,I,O): given ctx and term, find type
typeofIO :: Ctx -> Tm -> Stream Ty
typeofIO ctx0 e0 = runSubstKanren $ fresh $ \ty -> do
  _ <- embed $ typeof (Ground $ project ctx0) (Ground $ project e0) ty
  eval ty

-- Run type checking in mode (I,I,I): verify term has given type
checkIII :: Ctx -> Tm -> Ty -> Stream ()
checkIII ctx0 e0 ty0 = runSubstKanren $ do
  _ <- embed $ typeof (Ground $ project ctx0) (Ground $ project e0) (Ground $ project ty0)
  pure ()

main :: IO ()
main = do
  putStrLn "=== System F Type Checking ==="
  putStrLn ""

  -- Example 1: Unit value
  putStrLn "1. Typecheck: ()"
  putStrLn "   Expected: Unit"
  print $ takeS 1 (typeofIO Nil Unit)
  putStrLn ""

  -- Example 2: Identity function (monomorphic)
  -- λx:Unit. x : Unit → Unit
  let idUnit = Lam TUnit (Var Z)
  putStrLn "2. Typecheck: λx:Unit. x"
  putStrLn "   Expected: Unit → Unit"
  print $ takeS 1 (typeofIO Nil idUnit)
  putStrLn ""

  -- Example 3: Polymorphic identity
  -- Λα. λx:α. x : ∀α. α → α
  let polyId = TLam (Lam (TVar Z) (Var Z))
  putStrLn "3. Typecheck: Λα. λx:α. x"
  putStrLn "   Expected: ∀α. α → α"
  print $ takeS 1 (typeofIO Nil polyId)
  putStrLn ""

  -- Example 4: Apply polymorphic identity to Unit
  -- (Λα. λx:α. x) [Unit] : Unit → Unit
  let polyIdApp = TApp polyId TUnit
  putStrLn "4. Typecheck: (Λα. λx:α. x) [Unit]"
  putStrLn "   Expected: Unit → Unit"
  print $ takeS 1 (typeofIO Nil polyIdApp)
  putStrLn ""

  -- Example 5: Apply polymorphic identity to Unit value
  -- ((Λα. λx:α. x) [Unit]) () : Unit
  let fullApp = App polyIdApp Unit
  putStrLn "5. Typecheck: ((Λα. λx:α. x) [Unit]) ()"
  putStrLn "   Expected: Unit"
  print $ takeS 1 (typeofIO Nil fullApp)
  putStrLn ""

  -- Example 6: Church boolean type: ∀α. α → α → α
  -- True: Λα. λx:α. λy:α. x
  let churchBoolTy = TAll (TArr (TVar Z) (TArr (TVar Z) (TVar Z)))
  let churchTrue = TLam (Lam (TVar Z) (Lam (TVar Z) (Var (S Z))))
  putStrLn "6. Typecheck: Λα. λx:α. λy:α. x  (Church true)"
  putStrLn "   Expected: ∀α. α → α → α"
  print $ takeS 1 (typeofIO Nil churchTrue)
  putStrLn ""

  -- Example 7: Church false: Λα. λx:α. λy:α. y
  let churchFalse = TLam (Lam (TVar Z) (Lam (TVar Z) (Var Z)))
  putStrLn "7. Typecheck: Λα. λx:α. λy:α. y  (Church false)"
  putStrLn "   Expected: ∀α. α → α → α"
  print $ takeS 1 (typeofIO Nil churchFalse)
  putStrLn ""

  -- Example 8: Nested polymorphism
  -- Λα. Λβ. λx:α. λy:β. x : ∀α. ∀β. α → β → α
  let nested = TLam (TLam (Lam (TVar (S Z)) (Lam (TVar Z) (Var (S Z)))))
  putStrLn "8. Typecheck: Λα. Λβ. λx:α. λy:β. x"
  putStrLn "   Expected: ∀α. ∀β. α → β → α"
  print $ takeS 1 (typeofIO Nil nested)
  putStrLn ""

  -- Example 9: Type verification (checking mode)
  putStrLn "9. Verify: (Λα. λx:α. x) : ∀α. α → α"
  let polyIdTy = TAll (TArr (TVar Z) (TVar Z))
  print $ takeS 1 (checkIII Nil polyId polyIdTy)
  putStrLn ""

  -- Example 10: Apply nested polymorphism
  -- (Λα. Λβ. λx:α. λy:β. x) [Unit] [Unit → Unit]
  let nestedApp = TApp (TApp nested TUnit) (TArr TUnit TUnit)
  putStrLn "10. Typecheck: (Λα. Λβ. λx:α. λy:β. x) [Unit] [Unit → Unit]"
  putStrLn "    Expected: Unit → (Unit → Unit) → Unit"
  print $ takeS 1 (typeofIO Nil nestedApp)
  putStrLn ""

  -- Example 11: Self-application type (∀α. α → α) → (∀α. α → α)
  -- λf:(∀α. α → α). f [∀α. α → α] f
  let selfAppTy = TArr polyIdTy polyIdTy
  let selfApp = Lam polyIdTy (App (TApp (Var Z) polyIdTy) (Var Z))
  putStrLn "11. Typecheck: λf:(∀α. α → α). f [∀α. α → α] f"
  putStrLn "    Expected: (∀α. α → α) → (∀α. α → α)"
  print $ takeS 1 (typeofIO Nil selfApp)
  putStrLn ""

  -- Example 12: Term synthesis - find a term of type Unit → Unit
  putStrLn "12. Synthesize term of type Unit → Unit"
  let synthQuery = runSubstKanren $ fresh $ \e -> do
        _ <- embed $ typeof nil e (tarr tunit tunit)
        eval e
  print $ takeS 3 synthQuery
  putStrLn ""

  putStrLn "=== All examples complete ==="
