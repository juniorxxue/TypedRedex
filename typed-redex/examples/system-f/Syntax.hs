{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}

module Syntax where

import TypedRedex
import TypedRedex.Core.Internal.Logic (Logic)
import TypedRedex.Interp.Subst (runSubstRedex, takeS, Stream)
import TypedRedex.Interp.PrettyPrint (VarNaming(..), LogicVarNaming(..), natNaming, tyNaming, ctxNaming, subscriptNum)
import TypedRedex.DSL.TH (deriveLogicType, deriveLogicTypeNoNaming, (~>))
import TypedRedex.DSL.Type (quote0, quote1, quote2, quote3)

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

--------------------------------------------------------------------------------
-- Natural numbers for de Bruijn indices
--------------------------------------------------------------------------------

data Nat = Z | S Nat deriving (Eq, Show)

-- Custom naming: n, m, k, n₁, ...
instance LogicVarNaming Nat where
  varNaming = natNaming

deriveLogicTypeNoNaming ''Nat
  [ 'Z ~> ("Z", "zro")
  , 'S ~> ("S", "suc")
  ]

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

data Ty
  = TUnit        -- Unit type
  | TVar Nat     -- Type variable (de Bruijn index)
  | TArr Ty Ty   -- Function type: A → B
  | TAll Ty      -- Universal type: ∀α. A (binding increments indices)
  deriving (Eq, Show)

-- Custom naming: A, B, C, D, E, F, A₁, ...
instance LogicVarNaming Ty where
  varNaming = tyNaming

deriveLogicTypeNoNaming ''Ty
  [ 'TUnit ~> ("TUnit", "tunit")
  , 'TVar  ~> ("TVar", "tvar")
  , 'TArr  ~> ("TArr", "tarr")
  , 'TAll  ~> ("TAll", "tall")
  ]

--------------------------------------------------------------------------------
-- Terms
--------------------------------------------------------------------------------

data Tm
  = Unit          -- Unit value: ()
  | Var Nat       -- Term variable (de Bruijn index)
  | Lam Ty Tm     -- Term abstraction: λx:A. e
  | App Tm Tm     -- Term application: e₁ e₂
  | TLam Tm       -- Type abstraction: Λα. e
  | TApp Tm Ty    -- Type application: e [A]
  deriving (Eq, Show)

-- Custom naming: e₁, e₂, e₃, ... (starting from 1, not 0)
instance LogicVarNaming Tm where
  varNaming = VarNaming "E" (\i -> "e" ++ subscriptNum (i + 1))

deriveLogicTypeNoNaming ''Tm
  [ 'Unit ~> ("Unit", "unit'")
  , 'Var  ~> ("Var", "var")
  , 'Lam  ~> ("Lam", "lam")
  , 'App  ~> ("App", "app")
  , 'TLam ~> ("TLam", "tlam")
  , 'TApp ~> ("TApp", "tapp")
  ]

--------------------------------------------------------------------------------
-- Typing context
--------------------------------------------------------------------------------

-- Typing context: tracks both term and type bindings
-- Term bindings: actual types
-- Type bindings: just markers (type variables are represented by de Bruijn indices)
data Ctx
  = Nil
  | TmBind Ty Ctx   -- Term variable binding: x : A
  | TyBind Ctx      -- Type variable binding: α (marker for ∀ elimination)
  deriving (Eq, Show)

-- Custom naming: Γ, Γ₁, Γ₂, ...
instance LogicVarNaming Ctx where
  varNaming = ctxNaming

deriveLogicTypeNoNaming ''Ctx
  [ 'Nil    ~> ("Nil", "nil")
  , 'TmBind ~> ("TmBind", "tmBind")
  , 'TyBind ~> ("TyBind", "tyBind")
  ]
