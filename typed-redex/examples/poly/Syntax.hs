{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}

module Syntax where

import TypedRedex
import TypedRedex.Nominal
import TypedRedex.Nominal.Bind (Bind(..))
import TypedRedex.Nominal.Prelude
import TypedRedex.Nominal.Hash (Hash(..))
import TypedRedex.Interp.PrettyPrint (VarNaming(..), LogicVarNaming(..), subscriptNum)
import TypedRedex.DSL.TH (deriveLogicTypeNoNaming, derivePermute, deriveHash, (~>))
import TypedRedex.DSL.Type (quote0, quote1, quote2, quote3)
import TypedRedex.DSL.Moded (T(..), ground, Union)
import qualified Data.Set as S

-- Matches Poly/app/Syntax.hs

--------------------------------------------------------------------------------
-- Types (Ty)
-- data Ty = TInt | TBool | TVar TyName | TArr Ty Ty
--         | TForall (Bind TyName Ty) | TUncurry [Ty] Ty
--         | TList Ty | TProd Ty Ty | TST Ty Ty
--------------------------------------------------------------------------------

data Ty
  = TInt
  | TBool
  | TVar TyNom
  | TArr Ty Ty
  | TForall (Bind TyNom Ty)   -- forall a. ty
  | TList Ty                   -- [ty]
  | TProd Ty Ty                -- ty1 * ty2
  deriving (Eq, Show)

instance LogicVarNaming Ty where
  varNaming = VarNaming "T" (\i -> "ty" ++ show i)

derivePermute ''Ty [''TyNom]

-- Nom doesn't occur in Ty
instance Permute Nom Ty where
  swap _ _ ty = ty

instance Hash Nom Ty where
  occursIn _ _ = False

deriveLogicTypeNoNaming ''Ty
  [ 'TInt    ~> ("TInt", "tint")
  , 'TBool   ~> ("TBool", "tbool")
  , 'TVar    ~> ("TVar", "tvar")
  , 'TArr    ~> ("TArr", "tarr")
  , 'TForall ~> ("TForall", "tforall")
  , 'TList   ~> ("TList", "tlist")
  , 'TProd   ~> ("TProd", "tprod")
  ]

deriveHash ''Ty [''TyNom]

--------------------------------------------------------------------------------
-- Terms (Tm)
-- data Tm = LitInt Int | LitBool Bool | Var TmName
--         | Abs (Bind TmName Tm) | AbsAnn (Bind (TmName, Embed Ty) Tm)
--         | App Tm Tm | Ann Tm Ty
--         | TAbs (Bind TyName Tm) | TApp Tm Ty
--         | Nil | Pair Tm Tm | Fst Tm | Snd Tm
--------------------------------------------------------------------------------

data Tm
  = Var Nom
  | Abs (Bind Nom Tm)              -- λx. e
  | AbsAnn Ty (Bind Nom Tm)        -- λx:τ. e
  | App Tm Tm                      -- e1 e2
  | Ann Tm Ty                      -- e : τ
  | TAbs (Bind TyNom Tm)           -- Λα. e
  | TApp Tm Ty                     -- e @τ
  | Nil                            -- nil
  | Pair Tm Tm                     -- <e1, e2>
  | Fst Tm                         -- fst e
  | Snd Tm                         -- snd e
  deriving (Eq, Show)

instance LogicVarNaming Tm where
  varNaming = VarNaming "E" (\i -> "e" ++ show i)

derivePermute ''Tm [''TyNom, ''Nom]

-- Cross-nominal Permute instances for Bind and Ty in Tm
-- (Must come AFTER derivePermute which generates Permute Nom Tm, Permute TyNom Tm)
instance Permute Nom (Bind TyNom Tm) where
  swap a b (Bind n body) = Bind n (swap a b body)

instance Permute TyNom (Bind Nom Tm) where
  swap a b (Bind n body) = Bind n (swap a b body)

deriveLogicTypeNoNaming ''Tm
  [ 'Var     ~> ("Var", "var")
  , 'Abs     ~> ("Abs", "abs")
  , 'AbsAnn  ~> ("AbsAnn", "absAnn")
  , 'App     ~> ("App", "app")
  , 'Ann     ~> ("Ann", "ann")
  , 'TAbs    ~> ("TAbs", "tabs")
  , 'TApp    ~> ("TApp", "tapp")
  , 'Nil     ~> ("Nil", "nil")
  , 'Pair    ~> ("Pair", "pair")
  , 'Fst     ~> ("Fst", "fst'")
  , 'Snd     ~> ("Snd", "snd'")
  ]

deriveHash ''Tm [''TyNom, ''Nom]

-- Cross-nominal Hash instances (name type differs from binder type, so no shadowing)
instance Hash Nom (Bind TyNom Tm) where
  occursIn a (Bind _ body) = occursIn a body  -- TyNom doesn't shadow Nom

instance Hash TyNom (Bind Nom Tm) where
  occursIn a (Bind _ body) = occursIn a body  -- Nom doesn't shadow TyNom

--------------------------------------------------------------------------------
-- Polarity (Polar)
-- data Polar = Pos | Neg
--------------------------------------------------------------------------------

data Polar
  = Pos
  | Neg
  deriving (Eq, Show)

instance LogicVarNaming Polar where
  varNaming = VarNaming "P" (\i -> "p" ++ show i)

deriveLogicTypeNoNaming ''Polar
  [ 'Pos ~> ("Pos", "pos")
  , 'Neg ~> ("Neg", "neg")
  ]

--------------------------------------------------------------------------------
-- Environment (Env)
-- data Env = EEmpty | ETrm TmName Ty Env | EUvar TyName Env
--          | EEvar TyName Env | ESvar TyName Ty Env
--------------------------------------------------------------------------------

data Env
  = EEmpty                    -- ∅
  | ETrm Nom Ty Env           -- Γ, x : τ
  | EUvar TyNom Env           -- Γ, α
  | EEvar TyNom Env           -- Γ, ^α
  | ESvar TyNom Ty Env        -- Γ, α = τ
  deriving (Eq, Show)

instance LogicVarNaming Env where
  varNaming = VarNaming "Γ" (\i -> "Γ" ++ subscriptNum i)

derivePermute ''Env [''TyNom, ''Nom]

deriveLogicTypeNoNaming ''Env
  [ 'EEmpty ~> ("EEmpty", "eempty")
  , 'ETrm   ~> ("ETrm", "etrm")
  , 'EUvar  ~> ("EUvar", "euvar")
  , 'EEvar  ~> ("EEvar", "eevar")
  , 'ESvar  ~> ("ESvar", "esvar")
  ]

deriveHash ''Env [''TyNom, ''Nom]

--------------------------------------------------------------------------------
-- Pretty printing (matches Poly show instances)
--------------------------------------------------------------------------------

prettyTy :: Ty -> String
prettyTy TInt = "int"
prettyTy TBool = "bool"
prettyTy (TVar a) = prettyTyNom a
prettyTy (TArr t1 t2) = prettyTy t1 ++ " -> " ++ prettyTy t2
prettyTy (TForall (Bind a t)) = "forall " ++ prettyTyNom a ++ ". " ++ prettyTy t
prettyTy (TList t) = "[" ++ prettyTy t ++ "]"
prettyTy (TProd t1 t2) = prettyTy t1 ++ " * " ++ prettyTy t2

prettyTyNom :: TyNom -> String
prettyTyNom (TyNom n) = "a" ++ show n

prettyNom :: Nom -> String
prettyNom (Nom n) = "x" ++ show n

prettyPolar :: Polar -> String
prettyPolar Pos = "≤+"
prettyPolar Neg = "≤-"

prettyEnv :: Env -> String
prettyEnv EEmpty = "∅"
prettyEnv (ETrm x ty env) = prettyEnv env ++ ", " ++ prettyNom x ++ ":" ++ prettyTy ty
prettyEnv (EUvar a env) = prettyEnv env ++ ", " ++ prettyTyNom a
prettyEnv (EEvar a env) = prettyEnv env ++ ", " ++ prettyTyNom a ++ "^"
prettyEnv (ESvar a ty env) = prettyEnv env ++ ", " ++ prettyTyNom a ++ "=" ++ prettyTy ty
