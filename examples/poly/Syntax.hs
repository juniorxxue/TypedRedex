{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}

module Syntax where

import Prelude hiding (abs)
import TypedRedex hiding (neg)
import TypedRedex.Nominal
import TypedRedex.Nominal.Bind (Bind(..))
import TypedRedex.Nominal.Prelude
import TypedRedex.Nominal.Hash (Hash(..))
import TypedRedex.DSL.TH (deriveLogicType, derivePermute, deriveHash, deriveSubsto)
import qualified TypedRedex.DSL.TH as TH
import TypedRedex.DSL.Type (quote0, quote1, quote2, quote3)
import TypedRedex.DSL.Moded (T(..), ground, Union)
import TypedRedex.Interp.Display
import qualified Data.Set as S

--------------------------------------------------------------------------------
-- Data Types (defined first)
--------------------------------------------------------------------------------

data Ty
  = TInt
  | TTop
  | TBot
  | TVar TyNom
  | TArr Ty Ty
  | TForall (Bind TyNom Ty)
  deriving (Eq, Show)

data Tm
  = Literal Int
  | Var Nom
  | Abs (Bind Nom Tm)
  | App Tm Tm
  | Ann Tm Ty
  | TAbs (Bind TyNom Tm)
  | TApp Tm Ty
  deriving (Eq, Show)

data Polar
  = Pos
  | Neg
  deriving (Eq, Show)

data Env
  = EEmpty
  | ETrm Nom Ty Env
  | EUvar TyNom Env
  | EBound Ty TyNom Ty Env
  deriving (Eq, Show)

data Context
   = CEmpty
   | CType Ty
   | CTm Tm Context
   deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Display tables and HasDisplay instances (before deriveLogicType!)
--------------------------------------------------------------------------------

tyDisplay :: Display Ty
tyDisplay = display
  [ #TInt    ~= "int"
  , #TTop    ~= "top"
  , #TBot    ~= "bot"
  , #TVar    ~> \a -> (a :: D)
  , #TArr    ~> \(a, b) -> parens (a <+> " → " <+> b)
  , #TForall ~> \bnd -> "∀" <+> bnd
  ]

polarDisplay :: Display Polar
polarDisplay = display
  [ #Pos ~= "≤⁺"
  , #Neg ~= "≤⁻"
  ]

envDisplay :: Display Env
envDisplay = display
  [ #EEmpty ~= "·"
  , #ETrm   ~> \(x, ty, env) -> env <+> ", " <+> x <+> ":" <+> ty
  , #EUvar  ~> \(a, env) -> env <+> ", " <+> a
  , #EBound  ~> \(ty1, a, ty2, env) -> env <+> ", " <+> ty1 <+> "<:" <+> a <+> "<:" <+> ty2
  ]

contextDisplay :: Display Context
contextDisplay = display
  [ #CEmpty      ~= "□"
  , #CType       ~> \ty -> (ty :: D)
  , #CTm         ~> \(tm, ctx) -> tm <+> " ~> " <+> ctx
  ]

tmDisplay :: Display Tm
tmDisplay = display
  [ #Literal ~> \n -> (n :: D)                          -- literal number
  , #Var     ~> \x -> (x :: D)                          -- variable
  , #Abs     ~> \bnd -> "λ" <+> bnd                     -- λx.e
  , #App     ~> \(e1, e2) -> parens (e1 <+> " " <+> e2) -- (e₁ e₂)
  , #Ann     ~> \(e, ty) -> parens (e <+> " : " <+> ty) -- (e : A)
  , #TAbs    ~> \bnd -> "Λ" <+> bnd                     -- Λα.e
  , #TApp    ~> \(e, ty) -> e <+> "[" <+> ty <+> "]"    -- e[A]
  ]

instance HasDisplay Ty where
  typeNaming = cycleNames ["A", "B", "C", "D", "E", "F"]
  formatCon = formatWithDisplay tyDisplay

instance HasDisplay Polar where
  typeNaming = numberedNames "≤"
  formatCon = formatWithDisplay polarDisplay

instance HasDisplay Env where
  typeNaming = numberedNames "Γ"
  formatCon = formatWithDisplay envDisplay

instance HasDisplay Context where
  typeNaming = numberedNames "Σ"
  formatCon = formatWithDisplay contextDisplay

instance HasDisplay Tm where
  typeNaming = numberedNames "e"
  formatCon = formatWithDisplay tmDisplay

--------------------------------------------------------------------------------
-- Permute instances (before deriveLogicType)
--------------------------------------------------------------------------------

derivePermute ''Ty [''TyNom]

instance Permute Nom Ty where
  swap _ _ ty = ty

instance Hash Nom Ty where
  occursIn _ _ = False

derivePermute ''Tm [''TyNom, ''Nom]

instance Permute Nom (Bind TyNom Tm) where
  swap a b (Bind n body) = Bind n (swap a b body)

instance Permute TyNom (Bind Nom Tm) where
  swap a b (Bind n body) = Bind n (swap a b body)

derivePermute ''Env [''TyNom, ''Nom]

--------------------------------------------------------------------------------
-- LogicType derivations (now HasDisplay is available)
--------------------------------------------------------------------------------

deriveLogicType ''Ty
  [ 'TInt    TH.~> "tint"
  , 'TTop    TH.~> "ttop"
  , 'TBot    TH.~> "tbot"
  , 'TVar    TH.~> "tvar"
  , 'TArr    TH.~> "tarr"
  , 'TForall TH.~> "tforall"
  ]

deriveLogicType ''Tm
  [ 'Literal TH.~> "lit"
  , 'Var     TH.~> "var"
  , 'Abs     TH.~> "lam"
  , 'App     TH.~> "app"
  , 'Ann     TH.~> "ann"
  , 'TAbs    TH.~> "tlam"
  , 'TApp    TH.~> "tapp"
  ]

deriveLogicType ''Polar
  [ 'Pos TH.~> "pos"
  , 'Neg TH.~> "neg"
  ]

deriveLogicType ''Env
  [ 'EEmpty TH.~> "eempty"
  , 'ETrm   TH.~> "etrm"
  , 'EUvar  TH.~> "euvar"
  , 'EBound TH.~> "ebound"
  ]

deriveLogicType ''Context
  [ 'CEmpty TH.~> "cempty"
  , 'CType  TH.~> "ctype"
  , 'CTm    TH.~> "ctm"
  ]

--------------------------------------------------------------------------------
-- Hash derivations (after LogicType)
--------------------------------------------------------------------------------

deriveHash ''Ty [''TyNom]

deriveHash ''Tm [''TyNom, ''Nom]

instance Hash Nom (Bind TyNom Tm) where
  occursIn a (Bind _ body) = occursIn a body

instance Hash TyNom (Bind Nom Tm) where
  occursIn a (Bind _ body) = occursIn a body

deriveHash ''Env [''TyNom, ''Nom]

--------------------------------------------------------------------------------
-- Substitution derivation (uses Substo from TypedRedex.Nominal)
--------------------------------------------------------------------------------

-- | Capture-avoiding substitution: [replacement/alpha]body = result
-- TVar is the variable constructor for TyNom in Ty
deriveSubsto ''Ty [(''TyNom, 'TVar)]
