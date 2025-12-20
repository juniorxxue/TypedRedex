{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}

module Syntax where

import TypedRedex
import TypedRedex.Core.Internal.Redex (Redex)
import TypedRedex.Core.Internal.Logic (Logic)
import TypedRedex.DSL.Fresh (LTerm)
import TypedRedex.Nominal
import TypedRedex.Nominal.Bind (mkBindL)
import TypedRedex.Nominal.Prelude
import TypedRedex.Interp.Subst (runSubstRedex, takeS, Stream)
import TypedRedex.Interp.PrettyPrint (VarNaming(..), LogicVarNaming(..), ctxNaming, subscriptNum)
import TypedRedex.DSL.TH (deriveLogicType, deriveLogicTypeNoNaming, (~>))
import TypedRedex.DSL.Type (quote0, quote1, quote2, quote3)
import TypedRedex.DSL.Moded (T(..), ground, lift1, lift2, lift3, Union)

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
  [ 'TUnit ~> ("TUnit", "tunit")
  , 'TVar  ~> ("TVar", "tvar")
  , 'TArr  ~> ("TArr", "tarr")
  , 'TAll  ~> ("TAll", "tall")
  ]

-- Moded constructors for Ty
tunitM :: T '[] Ty rel
tunitM = ground tunit

tvarM :: T vs TyNom rel -> T vs Ty rel
tvarM = lift1 tvar

tarrM :: T vs1 Ty rel -> T vs2 Ty rel -> T (Union vs1 vs2) Ty rel
tarrM = lift2 tarr

tallM :: T vs (Bind TyNom Ty) rel -> T vs Ty rel
tallM = lift1 tall

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

-- Moded constructors for Tm
unitM :: T '[] Tm rel
unitM = ground unit'

varM :: T vs Nom rel -> T vs Tm rel
varM = lift1 var

lamM :: T vs1 Ty rel -> T vs2 (Bind Nom Tm) rel -> T (Union vs1 vs2) Tm rel
lamM = lift2 lam

appM :: T vs1 Tm rel -> T vs2 Tm rel -> T (Union vs1 vs2) Tm rel
appM = lift2 app

tlamM :: T vs (Bind TyNom Tm) rel -> T vs Tm rel
tlamM = lift1 tlam

tappM :: T vs1 Tm rel -> T vs2 Ty rel -> T (Union vs1 vs2) Tm rel
tappM = lift2 tapp

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
  [ 'Nil     ~> ("Nil", "nil")
  , 'TmBind  ~> ("TmBind", "tmBind")
  , 'TyBind' ~> ("TyBind'", "tyBind'")
  ]

-- Moded constructors for Ctx
nilM :: T '[] Ctx rel
nilM = ground nil

tmBindM :: T vs1 Nom rel -> T vs2 Ty rel -> T vs3 Ctx rel
        -> T (Union vs1 (Union vs2 vs3)) Ctx rel
tmBindM = lift3 tmBind

tyBindM :: T vs1 TyNom rel -> T vs2 Ctx rel -> T (Union vs1 vs2) Ctx rel
tyBindM = lift2 tyBind'

--------------------------------------------------------------------------------
-- Moded constructors for Bind (nominal binders)
--------------------------------------------------------------------------------

-- | Create a term binder from a ground Nom and a tracked body
bindNomM :: (Permute Nom body, LogicType body)
         => Nom -> T vs body rel -> T vs (Bind Nom body) rel
bindNomM n (T b) = T (bind n b)

-- | Create a type binder from a ground TyNom and a tracked body
bindTyNomM :: (Permute TyNom body, LogicType body)
           => TyNom -> T vs body rel -> T vs (Bind TyNom body) rel
bindTyNomM n (T b) = T (bind n b)

-- | Create a term binder pattern with tracked name and body.
-- The name is a logic variable (can unify with any Nom).
bindNomPatM :: (Redex rel, LogicType body, Permute Nom body)
            => T vs1 Nom rel -> T vs2 body rel
            -> T (Union vs1 vs2) (Bind Nom body) rel
bindNomPatM (T nameL) (T bodyL) = T (mkBindL nameL bodyL)

-- | Create a type binder pattern with tracked name and body.
-- The name is a logic variable (can unify with any TyNom).
bindTyPatM :: (Redex rel, LogicType body, Permute TyNom body)
           => T vs1 TyNom rel -> T vs2 body rel
           -> T (Union vs1 vs2) (Bind TyNom body) rel
bindTyPatM (T nameL) (T bodyL) = T (mkBindL nameL bodyL)

--------------------------------------------------------------------------------
-- Moded constructors for nominal atoms (ground, no variable tracking)
--------------------------------------------------------------------------------

nomM :: Nom -> T '[] Nom rel
nomM = ground . nom

tynomM :: TyNom -> T '[] TyNom rel
tynomM = ground . tynom
