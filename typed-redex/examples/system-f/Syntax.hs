{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}

module Syntax where

import TypedRedex
import TypedRedex.DSL.Fresh (LTerm)
import TypedRedex.Nominal
import TypedRedex.Nominal.Bind (mkBindL)
import TypedRedex.Nominal.Prelude
import TypedRedex.Interp.Subst (runSubstRedex, takeS, Stream)
import TypedRedex.Interp.PrettyPrint (VarNaming(..), LogicVarNaming(..), ctxNaming, subscriptNum)
import TypedRedex.DSL.TH (deriveLogicType, deriveLogicTypeNoNaming, (~>))
import TypedRedex.DSL.Type (quote0, quote1, quote2, quote3)
import TypedRedex.DSL.Moded (T(..), ground, lift1, lift2, lift3, Union)
import qualified Data.Set as S

-- System F Type Checking with Nominal Logic (Moded Version)
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
  [ 'TUnit ~> ("TUnit", "tunit_")
  , 'TVar  ~> ("TVar", "tvar_")
  , 'TArr  ~> ("TArr", "tarr_")
  , 'TAll  ~> ("TAll", "tall_")
  ]

-- Moded constructors for Ty
tunit :: T '[] Ty rel
tunit = ground tunit_

tvar :: T vs TyNom rel -> T vs Ty rel
tvar = lift1 tvar_

tarr :: T vs1 Ty rel -> T vs2 Ty rel -> T (Union vs1 vs2) Ty rel
tarr = lift2 tarr_

tall :: T vs (Bind TyNom Ty) rel -> T vs Ty rel
tall = lift1 tall_

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
  [ 'Unit ~> ("Unit", "unit_")
  , 'Var  ~> ("Var", "var_")
  , 'Lam  ~> ("Lam", "lam_")
  , 'App  ~> ("App", "app_")
  , 'TLam ~> ("TLam", "tlam_")
  , 'TApp ~> ("TApp", "tapp_")
  ]

-- Moded constructors for Tm
unit :: T '[] Tm rel
unit = ground unit_

var :: T vs Nom rel -> T vs Tm rel
var = lift1 var_

lam :: T vs1 Ty rel -> T vs2 (Bind Nom Tm) rel -> T (Union vs1 vs2) Tm rel
lam = lift2 lam_

app :: T vs1 Tm rel -> T vs2 Tm rel -> T (Union vs1 vs2) Tm rel
app = lift2 app_

tlam :: T vs (Bind TyNom Tm) rel -> T vs Tm rel
tlam = lift1 tlam_

tapp :: T vs1 Tm rel -> T vs2 Ty rel -> T (Union vs1 vs2) Tm rel
tapp = lift2 tapp_

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
  [ 'Nil     ~> ("Nil", "nil_")
  , 'TmBind  ~> ("TmBind", "tmBind_")
  , 'TyBind' ~> ("TyBind'", "tyBind_")
  ]

-- Moded constructors for Ctx
nil :: T '[] Ctx rel
nil = ground nil_

tmBind :: T vs1 Nom rel -> T vs2 Ty rel -> T vs3 Ctx rel
       -> T (Union vs1 (Union vs2 vs3)) Ctx rel
tmBind = lift3 tmBind_

tyBind :: T vs1 TyNom rel -> T vs2 Ctx rel -> T (Union vs1 vs2) Ctx rel
tyBind = lift2 tyBind_

--------------------------------------------------------------------------------
-- Moded constructors for Bind (nominal binders)
--------------------------------------------------------------------------------

-- | Create a term binder from a ground Nom and a tracked body
bindNom :: (Permute Nom body, LogicType body)
        => Nom -> T vs body rel -> T vs (Bind Nom body) rel
bindNom n (T vars b) = T vars (bind n b)

-- | Create a type binder from a ground TyNom and a tracked body
bindTyNom :: (Permute TyNom body, LogicType body)
          => TyNom -> T vs body rel -> T vs (Bind TyNom body) rel
bindTyNom n (T vars b) = T vars (bind n b)

-- | Create a term binder pattern with tracked name and body.
-- The name is a logic variable (can unify with any Nom).
bindNomPat :: (Redex rel, LogicType body, Permute Nom body)
           => T vs1 Nom rel -> T vs2 body rel
           -> T (Union vs1 vs2) (Bind Nom body) rel
bindNomPat (T vars1 nameL) (T vars2 bodyL) = T (S.union vars1 vars2) (mkBindL nameL bodyL)

-- | Create a type binder pattern with tracked name and body.
-- The name is a logic variable (can unify with any TyNom).
bindTyPat :: (Redex rel, LogicType body, Permute TyNom body)
          => T vs1 TyNom rel -> T vs2 body rel
          -> T (Union vs1 vs2) (Bind TyNom body) rel
bindTyPat (T vars1 nameL) (T vars2 bodyL) = T (S.union vars1 vars2) (mkBindL nameL bodyL)

--------------------------------------------------------------------------------
-- Moded constructors for nominal atoms (ground, no variable tracking)
--------------------------------------------------------------------------------

nomG :: Nom -> T '[] Nom rel
nomG = ground . nom

tynomG :: TyNom -> T '[] TyNom rel
tynomG = ground . tynom
