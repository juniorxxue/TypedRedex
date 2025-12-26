{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Mode-checked bidirectional typing rules using Indexed Free Monad.
--
-- This module demonstrates the indexed free monad approach to mode-checked
-- logic programming rules.
--
-- = Key Difference from typedredex-dsl
--
-- The do-notation now builds a pure 'IxFree' AST instead of executing
-- immediately. Interpretation happens later via 'interpretEval',
-- 'interpretTypeset', or 'interpretTrace'.
module Rules
  ( -- * Syntax
    Nat(..), Ty(..), Tm(..), Ctx(..)
  , zro, suc
  , tunit, tarr
  , var, unit, lam, lamAnn, app, ann
  , nil, cons
    -- * Judgments
  , lookupCtx, synth, check
    -- * Negation example
  , notInCtx
  ) where

import Prelude hiding ((>>=), (>>), return)
import Control.Applicative (empty)
import Data.Proxy (Proxy(..))

-- Import from typedredex-free instead of typedredex-dsl
import TypedRedex.Free
  ( LogicType(..), Logic(..), Field(..), RedexNeg
  , Mode(..), T(..)
  , Judgment2, Judgment3, defJudge2, defJudge3
  , fresh, fresh2, fresh3, fresh4, fresh5, prem, concl, neg
  , ground, lift1, lift2, Union
  , return, (>>=), (>>)
  )

--------------------------------------------------------------------------------
-- Natural numbers for de Bruijn indices
--------------------------------------------------------------------------------

data Nat = Z | S Nat deriving (Eq, Show)

instance LogicType Nat where
  data Reified Nat var = ZR | SR (Logic Nat var)

  project Z = ZR
  project (S n) = SR (Ground $ project n)

  reify ZR = Just Z
  reify (SR (Ground n)) = S <$> reify n
  reify _ = Nothing

  quote ZR = ("Z", [])
  quote (SR n) = ("S", [Field (Proxy :: Proxy Nat) n])

  children ZR = []
  children (SR n) = [Field (Proxy :: Proxy Nat) n]

  unifyVal _ ZR ZR = pure ()
  unifyVal unif (SR x) (SR y) = unif x y
  unifyVal _ _ _ = empty

  derefVal _ ZR = pure Z
  derefVal deref (SR n) = S <$> deref n

-- Raw constructors
zro_ :: Logic Nat var
zro_ = Ground ZR

suc_ :: Logic Nat var -> Logic Nat var
suc_ = Ground . SR

-- Moded constructors
zro :: T '[] Nat rel
zro = ground zro_

suc :: T vs Nat rel -> T vs Nat rel
suc = lift1 suc_

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

data Ty = TUnit | TArr Ty Ty deriving (Eq, Show)

instance LogicType Ty where
  data Reified Ty var
    = TUnitR
    | TArrR (Logic Ty var) (Logic Ty var)

  project TUnit = TUnitR
  project (TArr a b) = TArrR (Ground $ project a) (Ground $ project b)

  reify TUnitR = Just TUnit
  reify (TArrR (Ground a) (Ground b)) = TArr <$> reify a <*> reify b
  reify _ = Nothing

  quote TUnitR = ("Unit", [])
  quote (TArrR a b) = ("→", [Field (Proxy :: Proxy Ty) a, Field (Proxy :: Proxy Ty) b])

  children TUnitR = []
  children (TArrR a b) = [Field (Proxy :: Proxy Ty) a, Field (Proxy :: Proxy Ty) b]

  unifyVal _ TUnitR TUnitR = pure ()
  unifyVal unif (TArrR a b) (TArrR a' b') = unif a a' *> unif b b'
  unifyVal _ _ _ = empty

  derefVal _ TUnitR = pure TUnit
  derefVal deref (TArrR a b) = TArr <$> deref a <*> deref b

tunit_ :: Logic Ty var
tunit_ = Ground TUnitR

tarr_ :: Logic Ty var -> Logic Ty var -> Logic Ty var
tarr_ a b = Ground $ TArrR a b

-- Moded
tunit :: T '[] Ty rel
tunit = ground tunit_

tarr :: T vs1 Ty rel -> T vs2 Ty rel -> T (Union vs1 vs2) Ty rel
tarr = lift2 tarr_

--------------------------------------------------------------------------------
-- Terms
--------------------------------------------------------------------------------

data Tm
  = Var Nat
  | Unit
  | Lam Tm
  | LamAnn Ty Tm
  | App Tm Tm
  | Ann Tm Ty
  deriving (Eq, Show)

instance LogicType Tm where
  data Reified Tm var
    = VarR (Logic Nat var)
    | UnitR
    | LamR (Logic Tm var)
    | LamAnnR (Logic Ty var) (Logic Tm var)
    | AppR (Logic Tm var) (Logic Tm var)
    | AnnR (Logic Tm var) (Logic Ty var)

  project (Var n) = VarR (Ground $ project n)
  project Unit = UnitR
  project (Lam b) = LamR (Ground $ project b)
  project (LamAnn ty b) = LamAnnR (Ground $ project ty) (Ground $ project b)
  project (App f a) = AppR (Ground $ project f) (Ground $ project a)
  project (Ann e ty) = AnnR (Ground $ project e) (Ground $ project ty)

  reify (VarR (Ground n)) = Var <$> reify n
  reify UnitR = Just Unit
  reify (LamR (Ground b)) = Lam <$> reify b
  reify (LamAnnR (Ground ty) (Ground b)) = LamAnn <$> reify ty <*> reify b
  reify (AppR (Ground f) (Ground a)) = App <$> reify f <*> reify a
  reify (AnnR (Ground e) (Ground ty)) = Ann <$> reify e <*> reify ty
  reify _ = Nothing

  quote (VarR n) = ("Var", [Field (Proxy :: Proxy Nat) n])
  quote UnitR = ("()", [])
  quote (LamR b) = ("λ", [Field (Proxy :: Proxy Tm) b])
  quote (LamAnnR ty b) = ("λ:", [Field (Proxy :: Proxy Ty) ty, Field (Proxy :: Proxy Tm) b])
  quote (AppR f a) = ("App", [Field (Proxy :: Proxy Tm) f, Field (Proxy :: Proxy Tm) a])
  quote (AnnR e ty) = (":", [Field (Proxy :: Proxy Tm) e, Field (Proxy :: Proxy Ty) ty])

  children (VarR n) = [Field (Proxy :: Proxy Nat) n]
  children UnitR = []
  children (LamR b) = [Field (Proxy :: Proxy Tm) b]
  children (LamAnnR ty b) = [Field (Proxy :: Proxy Ty) ty, Field (Proxy :: Proxy Tm) b]
  children (AppR f a) = [Field (Proxy :: Proxy Tm) f, Field (Proxy :: Proxy Tm) a]
  children (AnnR e ty) = [Field (Proxy :: Proxy Tm) e, Field (Proxy :: Proxy Ty) ty]

  unifyVal unif (VarR n) (VarR n') = unif n n'
  unifyVal _ UnitR UnitR = pure ()
  unifyVal unif (LamR b) (LamR b') = unif b b'
  unifyVal unif (LamAnnR ty b) (LamAnnR ty' b') = unif ty ty' *> unif b b'
  unifyVal unif (AppR f a) (AppR f' a') = unif f f' *> unif a a'
  unifyVal unif (AnnR e ty) (AnnR e' ty') = unif e e' *> unif ty ty'
  unifyVal _ _ _ = empty

  derefVal deref (VarR n) = Var <$> deref n
  derefVal _ UnitR = pure Unit
  derefVal deref (LamR b) = Lam <$> deref b
  derefVal deref (LamAnnR ty b) = LamAnn <$> deref ty <*> deref b
  derefVal deref (AppR f a) = App <$> deref f <*> deref a
  derefVal deref (AnnR e ty) = Ann <$> deref e <*> deref ty

var_ :: Logic Nat var -> Logic Tm var
var_ = Ground . VarR

unit_ :: Logic Tm var
unit_ = Ground UnitR

lam_ :: Logic Tm var -> Logic Tm var
lam_ = Ground . LamR

lamAnn_ :: Logic Ty var -> Logic Tm var -> Logic Tm var
lamAnn_ ty b = Ground $ LamAnnR ty b

app_ :: Logic Tm var -> Logic Tm var -> Logic Tm var
app_ f a = Ground $ AppR f a

ann_ :: Logic Tm var -> Logic Ty var -> Logic Tm var
ann_ e ty = Ground $ AnnR e ty

-- Moded
var :: T vs Nat rel -> T vs Tm rel
var = lift1 var_

unit :: T '[] Tm rel
unit = ground unit_

lam :: T vs Tm rel -> T vs Tm rel
lam = lift1 lam_

lamAnn :: T vs1 Ty rel -> T vs2 Tm rel -> T (Union vs1 vs2) Tm rel
lamAnn = lift2 lamAnn_

app :: T vs1 Tm rel -> T vs2 Tm rel -> T (Union vs1 vs2) Tm rel
app = lift2 app_

ann :: T vs1 Tm rel -> T vs2 Ty rel -> T (Union vs1 vs2) Tm rel
ann = lift2 ann_

--------------------------------------------------------------------------------
-- Type contexts
--------------------------------------------------------------------------------

data Ctx = Nil | Cons Ty Ctx deriving (Eq, Show)

instance LogicType Ctx where
  data Reified Ctx var
    = NilR
    | ConsR (Logic Ty var) (Logic Ctx var)

  project Nil = NilR
  project (Cons ty ctx) = ConsR (Ground $ project ty) (Ground $ project ctx)

  reify NilR = Just Nil
  reify (ConsR (Ground ty) (Ground ctx)) = Cons <$> reify ty <*> reify ctx
  reify _ = Nothing

  quote NilR = ("·", [])
  quote (ConsR ty ctx) = (",", [Field (Proxy :: Proxy Ty) ty, Field (Proxy :: Proxy Ctx) ctx])

  children NilR = []
  children (ConsR ty ctx) = [Field (Proxy :: Proxy Ty) ty, Field (Proxy :: Proxy Ctx) ctx]

  unifyVal _ NilR NilR = pure ()
  unifyVal unif (ConsR ty ctx) (ConsR ty' ctx') = unif ty ty' *> unif ctx ctx'
  unifyVal _ _ _ = empty

  derefVal _ NilR = pure Nil
  derefVal deref (ConsR ty ctx) = Cons <$> deref ty <*> deref ctx

nil_ :: Logic Ctx var
nil_ = Ground NilR

cons_ :: Logic Ty var -> Logic Ctx var -> Logic Ctx var
cons_ ty ctx = Ground $ ConsR ty ctx

-- Moded
nil :: T '[] Ctx rel
nil = ground nil_

cons :: T vs1 Ty rel -> T vs2 Ctx rel -> T (Union vs1 vs2) Ctx rel
cons = lift2 cons_

--------------------------------------------------------------------------------
-- Mode-checked lookup: Γ(n) = A
-- Modes: I, I, O
--------------------------------------------------------------------------------

lookupCtx :: RedexNeg rel => Judgment3 rel "lookup" '[ 'I, 'I, 'O] Ctx Nat Ty
lookupCtx = defJudge3 @"lookup" $ \rule ->
  [ rule "lookup-here" $ do
      (ty, rest) <- fresh2
      concl $ lookupCtx (cons ty rest) zro ty

  , rule "lookup-there" $ do
      (ty', rest, n', ty) <- fresh4
      concl $ lookupCtx (cons ty' rest) (suc n') ty
      prem $ lookupCtx rest n' ty
  ]

--------------------------------------------------------------------------------
-- Mode-checked synthesis: Γ ⊢ e ⇒ A
-- Modes: I, I, O
--------------------------------------------------------------------------------

synth :: RedexNeg rel => Judgment3 rel "synth" '[ 'I, 'I, 'O] Ctx Tm Ty
synth = defJudge3 @"synth" $ \rule ->
  [ -- ⇒Var
    rule "⇒Var" $ do
      (ctx, n, ty) <- fresh3
      concl $ synth ctx (var n) ty
      prem $ lookupCtx ctx n ty

  , -- ⇒Unit
    rule "⇒Unit" $ do
      ctx <- fresh
      concl $ synth ctx unit tunit

  , -- ⇒λ:
    rule "⇒λ:" $ do
      (ctx, a, b, body) <- fresh4
      concl $ synth ctx (lamAnn a body) (tarr a b)
      prem $ synth (cons a ctx) body b

  , -- ⇒App
    rule "⇒App" $ do
      (ctx, e1, e2, a, b) <- fresh5
      concl $ synth ctx (app e1 e2) b
      prem $ synth ctx e1 (tarr a b)
      prem $ check ctx e2 a

  , -- ⇒Ann
    rule "⇒Ann" $ do
      (ctx, e, ty) <- fresh3
      concl $ synth ctx (ann e ty) ty
      prem $ check ctx e ty
  ]

--------------------------------------------------------------------------------
-- Mode-checked checking: Γ ⊢ e ⇐ A
-- Modes: I, I, I
--------------------------------------------------------------------------------

check :: RedexNeg rel => Judgment3 rel "check" '[ 'I, 'I, 'I] Ctx Tm Ty
check = defJudge3 @"check" $ \rule ->
  [ -- ⇐λ
    rule "⇐λ" $ do
      (ctx, a, b, body) <- fresh4
      concl $ check ctx (lam body) (tarr a b)
      prem $ check (cons a ctx) body b

  , -- ⇐Sub
    rule "⇐Sub" $ do
      (ctx, e, ty) <- fresh3
      concl $ check ctx e ty
      prem $ synth ctx e ty
  ]

--------------------------------------------------------------------------------
-- Negation Example: notInCtx Γ n
-- Succeeds if index n is NOT in context Γ
--------------------------------------------------------------------------------

notInCtx :: RedexNeg rel => Judgment2 rel "notInCtx" '[ 'I, 'I] Ctx Nat
notInCtx = defJudge2 @"notInCtx" $ \rule ->
  [ -- notInCtx-empty
    rule "notInCtx-empty" $ do
      n <- fresh
      concl $ notInCtx nil n

  , -- notInCtx-cons
    rule "notInCtx-cons" $ do
      (ty, ctx, n) <- fresh3
      concl $ notInCtx (cons ty ctx) (suc n)
      neg $ lookupCtx (cons ty ctx) (suc n) ty
      prem $ notInCtx ctx n
  ]
