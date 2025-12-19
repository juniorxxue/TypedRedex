{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Syntax where

import TypedRedex
import TypedRedex.Core.Internal.Logic (Logic)
import TypedRedex.Nominal
import TypedRedex.Nominal.Prelude
import TypedRedex.Interp.Subst (runSubstRedex, takeS, Stream)
import TypedRedex.Interp.PrettyPrint (VarNaming(..), LogicVarNaming(..), ctxNaming, subscriptNum)
import TypedRedex.DSL.TH (deriveLogicType, deriveLogicTypeNoNaming, (~>))
import TypedRedex.DSL.Type (quote0, quote1, quote2, quote3)

-- System F Type Checking with Nominal Logic
-- Uses named variables (Nom, TyNom) instead of de Bruijn indices
--
-- Types:
--   tau ::= Unit | alpha | tau1 -> tau2 | forall alpha. tau
--
-- Terms:
--   e ::= () | x | lambda x:tau. e | e1 e2 | Lambda alpha. e | e [tau]
--
-- Typing rules:
--   Gamma(x) = A              Gamma |- () : Unit
--   -------------
--   Gamma |- x : A
--
--   Gamma, x:A |- e : B        Gamma |- e1 : A -> B    Gamma |- e2 : A
--   -------------------        -----------------------------------
--   Gamma |- lambda x:A. e : A -> B   Gamma |- e1 e2 : B
--
--   Gamma, alpha |- e : A          Gamma |- e : forall alpha. A
--   --------------------           ----------------------------
--   Gamma |- Lambda alpha. e : forall alpha. A     Gamma |- e [B] : A[alpha:=B]

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

data Ty
  = TUnit                   -- Unit type
  | TVar TyNom              -- Type variable (named)
  | TArr Ty Ty              -- Function type: A -> B
  | TAll (Bind TyNom Ty)    -- Universal type: forall alpha. A
  deriving (Eq, Show)

-- Custom naming: A, B, C, D, E, F, A1, ...
instance LogicVarNaming Ty where
  varNaming = VarNaming "T" (\i -> "ty" ++ show i)

deriveLogicTypeNoNaming ''Ty
  [ 'TUnit ~> ("TUnit", "tunit")
  , 'TVar  ~> ("TVar", "tvar")
  , 'TArr  ~> ("TArr", "tarr")
  , 'TAll  ~> ("TAll", "tall")
  ]

--------------------------------------------------------------------------------
-- Permute instance for Ty (required for Bind)
--------------------------------------------------------------------------------

-- Permute TyNom in Ty (for alpha-equivalence in type binders)
instance Permute TyNom Ty where
  swap a b TUnit = TUnit
  swap a b (TVar v) = TVar (swap a b v)
  swap a b (TArr t1 t2) = TArr (swap a b t1) (swap a b t2)
  swap a b (TAll bnd) = TAll (swap a b bnd)

-- Nom doesn't affect Ty
instance Permute Nom Ty where
  swap _ _ ty = ty

--------------------------------------------------------------------------------
-- Subst instance for Ty (required for instantiate)
--------------------------------------------------------------------------------

instance Subst TyNom Ty where
  subst name replacement ty = case ty of
    TUnit -> TUnit
    TVar v
      | v == name -> replacement
      | otherwise -> TVar v
    TArr t1 t2 -> TArr (subst name replacement t1) (subst name replacement t2)
    TAll bnd -> TAll (substBind name replacement bnd)

--------------------------------------------------------------------------------
-- Hash instances for Ty (checking if name occurs free)
--------------------------------------------------------------------------------

-- Check if TyNom occurs free in Ty
instance Hash TyNom Ty where
  occursIn a TUnit = False
  occursIn a (TVar v) = a == v
  occursIn a (TArr t1 t2) = occursIn a t1 || occursIn a t2
  occursIn a (TAll (Bind b body))
    | a == b    = False  -- shadowed
    | otherwise = occursIn a body

-- Nom never occurs in Ty (different namespace)
instance Hash Nom Ty where
  occursIn _ _ = False

--------------------------------------------------------------------------------
-- Terms
--------------------------------------------------------------------------------

data Tm
  = Unit                        -- Unit value: ()
  | Var Nom                     -- Term variable (named)
  | Lam Ty (Bind Nom Tm)        -- Term abstraction: lambda x:A. e
  | App Tm Tm                   -- Term application: e1 e2
  | TLam (Bind TyNom Tm)        -- Type abstraction: Lambda alpha. e
  | TApp Tm Ty                  -- Type application: e [A]
  deriving (Eq, Show)

-- Custom naming: e1, e2, e3, ... (starting from 1, not 0)
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
-- Permute instances for Tm
--------------------------------------------------------------------------------

-- Permute Nom in Tm (for alpha-equivalence in term binders)
instance Permute Nom Tm where
  swap a b Unit = Unit
  swap a b (Var v) = Var (swap a b v)
  swap a b (Lam ty bnd) = Lam ty (swap a b bnd)  -- ty doesn't contain Nom
  swap a b (App t1 t2) = App (swap a b t1) (swap a b t2)
  swap a b (TLam bnd) = TLam (swap a b bnd)
  swap a b (TApp t ty) = TApp (swap a b t) ty  -- ty doesn't contain Nom

-- Permute TyNom in Tm (type variables in terms)
instance Permute TyNom Tm where
  swap a b Unit = Unit
  swap a b (Var v) = Var v  -- term vars unaffected by type var swap
  swap a b (Lam ty bnd) = Lam (swap a b ty) (swap a b bnd)
  swap a b (App t1 t2) = App (swap a b t1) (swap a b t2)
  swap a b (TLam bnd) = TLam (swap a b bnd)
  swap a b (TApp t ty) = TApp (swap a b t) (swap a b ty)

-- Cross: Nom in Bind TyNom Tm (Nom swap doesn't affect TyNom)
instance Permute Nom (Bind TyNom Tm) where
  swap a b (Bind n body) = Bind n (swap a b body)

-- Cross: TyNom in Bind Nom Tm (TyNom swap doesn't affect Nom)
instance Permute TyNom (Bind Nom Tm) where
  swap a b (Bind n body) = Bind n (swap a b body)

--------------------------------------------------------------------------------
-- Hash instances for Tm (checking if name occurs free)
--------------------------------------------------------------------------------

-- Check if Nom occurs free in Tm
instance Hash Nom Tm where
  occursIn a Unit = False
  occursIn a (Var v) = a == v
  occursIn a (Lam _ (Bind b body))
    | a == b    = False  -- shadowed
    | otherwise = occursIn a body
  occursIn a (App t1 t2) = occursIn a t1 || occursIn a t2
  occursIn a (TLam (Bind _ body)) = occursIn a body  -- TyNom doesn't shadow Nom
  occursIn a (TApp t _) = occursIn a t  -- ty has no Nom

-- Check if TyNom occurs free in Tm
instance Hash TyNom Tm where
  occursIn _ Unit = False
  occursIn _ (Var _) = False  -- term vars don't contain type vars
  occursIn a (Lam ty (Bind _ body)) = occursIn a ty || occursIn a body
  occursIn a (App t1 t2) = occursIn a t1 || occursIn a t2
  occursIn a (TLam (Bind b body))
    | a == b    = False  -- shadowed
    | otherwise = occursIn a body
  occursIn a (TApp t ty) = occursIn a t || occursIn a ty

--------------------------------------------------------------------------------
-- Type substitution in terms (TyNom -> Ty in Tm)
-- Note: This is different from Subst typeclass which is same-type substitution
--------------------------------------------------------------------------------

-- | Substitute a type variable with a type in a term
substTyInTm :: TyNom -> Ty -> Tm -> Tm
substTyInTm name replacement tm = case tm of
  Unit -> Unit
  Var v -> Var v
  Lam ty bnd -> Lam (subst name replacement ty) (substTyInBind name replacement bnd)
  App t1 t2 -> App (substTyInTm name replacement t1) (substTyInTm name replacement t2)
  TLam (Bind v body)
    | v == name -> TLam (Bind v body)  -- shadowed
    | otherwise -> TLam (Bind v (substTyInTm name replacement body))
  TApp t ty -> TApp (substTyInTm name replacement t) (subst name replacement ty)

-- Helper: substitute type in term binder
substTyInBind :: TyNom -> Ty -> Bind Nom Tm -> Bind Nom Tm
substTyInBind name replacement (Bind n body) = Bind n (substTyInTm name replacement body)

--------------------------------------------------------------------------------
-- Typing context
--------------------------------------------------------------------------------

-- Typing context: tracks both term and type bindings
data Ctx
  = Nil
  | TmBind Nom Ty Ctx      -- Term variable binding: x : A
  | TyBind' TyNom Ctx      -- Type variable binding: alpha
  deriving (Eq, Show)

-- Custom naming: Gamma, Gamma1, Gamma2, ...
instance LogicVarNaming Ctx where
  varNaming = ctxNaming

deriveLogicTypeNoNaming ''Ctx
  [ 'Nil     ~> ("Nil", "nil")
  , 'TmBind  ~> ("TmBind", "tmBind")
  , 'TyBind' ~> ("TyBind'", "tyBind'")
  ]
