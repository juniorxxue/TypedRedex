{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Syntax where

import Control.Applicative (empty)
import TypedRedex.Core.Redex
import TypedRedex.Core.Internal.Logic (Logic (Ground), LogicType (..))
import TypedRedex.Interpreters.SubstRedex (runSubstRedex, takeS, Stream)
import TypedRedex.Utils.Type (quote0, quote1, quote2)

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
