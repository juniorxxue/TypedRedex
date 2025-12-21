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
import TypedRedex.DSL.TH (deriveLogicTypeNoNaming, derivePermute, deriveHash, deriveSubst, (~>))
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

-- NOTE: Permute must be derived BEFORE LogicType because Bind needs it
-- Generates: instance Permute TyNom Ty (structural swap)
derivePermute ''Ty [''TyNom]

-- Nom doesn't affect Ty (identity swap)
instance Permute Nom Ty where
  swap _ _ ty = ty

-- Generates: LogicType instance and moded constructors (tunit, tvar, tarr, tall)
deriveLogicTypeNoNaming ''Ty
  [ 'TUnit ~> ("TUnit", "tunit")
  , 'TVar  ~> ("TVar", "tvar")
  , 'TArr  ~> ("TArr", "tarr")
  , 'TAll  ~> ("TAll", "tall")
  ]

-- Generates: instance Hash TyNom Ty (with TAll shadowing)
deriveHash ''Ty [''TyNom]

-- Nom never occurs in Ty
instance Hash Nom Ty where
  occursIn _ _ = False

-- Generates: instance Subst TyNom Ty (with substBind for TAll)
deriveSubst ''Ty ''TyNom
  [ ('TAll, [| \n r bnd -> TAll (substBind n r bnd) |])
  ]

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

-- NOTE: Permute must be derived BEFORE LogicType because Bind needs it
-- Generates: instance Permute Nom Tm, instance Permute TyNom Tm
derivePermute ''Tm [''Nom, ''TyNom]

-- Cross-namespace Permute instances (Nom swap in Bind TyNom, and vice versa)
-- These can't be auto-derived because they cross binding namespaces
instance Permute Nom (Bind TyNom Tm) where
  swap a b (Bind n body) = Bind n (swap a b body)

instance Permute TyNom (Bind Nom Tm) where
  swap a b (Bind n body) = Bind n (swap a b body)

-- Generates: LogicType instance and moded constructors
deriveLogicTypeNoNaming ''Tm
  [ 'Unit ~> ("Unit", "unit")
  , 'Var  ~> ("Var", "var")
  , 'Lam  ~> ("Lam", "lam")
  , 'App  ~> ("App", "app")
  , 'TLam ~> ("TLam", "tlam")
  , 'TApp ~> ("TApp", "tapp")
  ]

-- Hash instances for Tm - manual because of cross-binder complexity
-- (Lam binds Nom but doesn't shadow TyNom, TLam binds TyNom but doesn't shadow Nom)
instance Hash Nom Tm where
  occursIn a Unit = False
  occursIn a (Var v) = a == v
  occursIn a (Lam _ (Bind b body))
    | a == b    = False  -- shadowed by term binder
    | otherwise = occursIn a body
  occursIn a (App t1 t2) = occursIn a t1 || occursIn a t2
  occursIn a (TLam (Bind _ body)) = occursIn a body  -- TyNom doesn't shadow Nom
  occursIn a (TApp t _) = occursIn a t  -- ty has no Nom

instance Hash TyNom Tm where
  occursIn _ Unit = False
  occursIn _ (Var _) = False  -- term vars don't contain type vars
  occursIn a (Lam ty (Bind _ body)) = occursIn a ty || occursIn a body  -- Nom doesn't shadow TyNom
  occursIn a (App t1 t2) = occursIn a t1 || occursIn a t2
  occursIn a (TLam (Bind b body))
    | a == b    = False  -- shadowed by type binder
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

-- Generates: LogicType instance and moded constructors
deriveLogicTypeNoNaming ''Ctx
  [ 'Nil     ~> ("Nil", "nil")
  , 'TmBind  ~> ("TmBind", "tmBind")
  , 'TyBind' ~> ("TyBind'", "tyBind")
  ]

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
