{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE FlexibleContexts #-}

-- | Bidirectional STLC with mode-checked rules.
--
-- This example demonstrates how to use the moded DSL for compile-time
-- verification that all rules have valid execution schedules.
module Main (main) where

import Control.Applicative (empty)
import TypedRedex hiding (fresh, fresh2, fresh3, fresh4, fresh5, ground, lift1, lift2, lift3)
import TypedRedex.Core.Internal.Logic (Logic (Ground), LogicType (..), Reified)
import TypedRedex.Interp.Subst (runSubstRedex, takeS, Stream)
import TypedRedex.Interp.PrettyPrint (LogicVarNaming(..))
import TypedRedex.DSL.Type (quote0, quote1, quote2)
import TypedRedex.DSL.Fresh (LTerm)
import qualified TypedRedex.DSL.Fresh as F
import qualified TypedRedex.DSL.Moded as R
import TypedRedex.DSL.Moded
  ( Mode(..), ModeList(..), T(..), TArgs(..)
  , AppliedM(..), mjudge3, toApplied, ToLTermList(..), ModedRule(..), ruleM
  , fresh, prem, concl
  , ground, lift1, lift2, Union
  )

--------------------------------------------------------------------------------
-- Natural numbers for de Bruijn indices
--------------------------------------------------------------------------------

data Nat = Z | S Nat deriving (Eq, Show)

instance LogicVarNaming Nat

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

-- Raw constructors
zro :: Logic Nat var
zro = Ground ZR

suc :: Logic Nat var -> Logic Nat var
suc = Ground . SR

-- Moded constructors (track variable sets)
zroM :: T '[] Nat rel
zroM = ground zro

sucM :: T vs Nat rel -> T vs Nat rel
sucM = lift1 suc

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

data Ty = TUnit | TArr Ty Ty deriving (Eq, Show)

instance LogicVarNaming Ty

instance LogicType Ty where
  data Reified Ty var
    = TUnitR
    | TArrR (Logic Ty var) (Logic Ty var)

  project TUnit = TUnitR
  project (TArr a b) = TArrR (Ground $ project a) (Ground $ project b)

  reify TUnitR = Just TUnit
  reify (TArrR (Ground a) (Ground b)) = TArr <$> reify a <*> reify b
  reify _ = Nothing

  quote TUnitR = quote0 "Unit" TUnitR
  quote (TArrR a b) = quote2 "→" TArrR a b

  unifyVal _ TUnitR TUnitR = pure ()
  unifyVal unif (TArrR a b) (TArrR a' b') = unif a a' *> unif b b'
  unifyVal _ _ _ = empty

  derefVal _ TUnitR = pure TUnit
  derefVal deref (TArrR a b) = TArr <$> deref a <*> deref b

tunit :: Logic Ty var
tunit = Ground TUnitR

tarr :: Logic Ty var -> Logic Ty var -> Logic Ty var
tarr a b = Ground $ TArrR a b

-- Moded
tunitM :: T '[] Ty rel
tunitM = ground tunit

tarrM :: T vs1 Ty rel -> T vs2 Ty rel -> T (Union vs1 vs2) Ty rel
tarrM = lift2 tarr

--------------------------------------------------------------------------------
-- Terms
--------------------------------------------------------------------------------

data Tm
  = Var Nat           -- x
  | Unit              -- ()
  | Lam Tm            -- λx.e (no annotation)
  | LamAnn Ty Tm      -- λx:A.e (annotated)
  | App Tm Tm         -- e₁ e₂
  | Ann Tm Ty         -- (e : A)
  deriving (Eq, Show)

instance LogicVarNaming Tm

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

  quote (VarR n) = quote1 "Var" VarR n
  quote UnitR = quote0 "()" UnitR
  quote (LamR b) = quote1 "λ" LamR b
  quote (LamAnnR ty b) = quote2 "λ:" LamAnnR ty b
  quote (AppR f a) = quote2 "App" AppR f a
  quote (AnnR e ty) = quote2 ":" AnnR e ty

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

var :: Logic Nat var -> Logic Tm var
var = Ground . VarR

unit' :: Logic Tm var
unit' = Ground UnitR

lam :: Logic Tm var -> Logic Tm var
lam = Ground . LamR

lamAnn :: Logic Ty var -> Logic Tm var -> Logic Tm var
lamAnn ty b = Ground $ LamAnnR ty b

app :: Logic Tm var -> Logic Tm var -> Logic Tm var
app f a = Ground $ AppR f a

ann :: Logic Tm var -> Logic Ty var -> Logic Tm var
ann e ty = Ground $ AnnR e ty

-- Moded
varM :: T vs Nat rel -> T vs Tm rel
varM = lift1 var

unitM :: T '[] Tm rel
unitM = ground unit'

lamM :: T vs Tm rel -> T vs Tm rel
lamM = lift1 lam

lamAnnM :: T vs1 Ty rel -> T vs2 Tm rel -> T (Union vs1 vs2) Tm rel
lamAnnM = lift2 lamAnn

appM :: T vs1 Tm rel -> T vs2 Tm rel -> T (Union vs1 vs2) Tm rel
appM = lift2 app

annM :: T vs1 Tm rel -> T vs2 Ty rel -> T (Union vs1 vs2) Tm rel
annM = lift2 ann

--------------------------------------------------------------------------------
-- Type contexts
--------------------------------------------------------------------------------

data Ctx = Nil | Cons Ty Ctx deriving (Eq, Show)

instance LogicVarNaming Ctx

instance LogicType Ctx where
  data Reified Ctx var
    = NilR
    | ConsR (Logic Ty var) (Logic Ctx var)

  project Nil = NilR
  project (Cons ty ctx) = ConsR (Ground $ project ty) (Ground $ project ctx)

  reify NilR = Just Nil
  reify (ConsR (Ground ty) (Ground ctx)) = Cons <$> reify ty <*> reify ctx
  reify _ = Nothing

  quote NilR = quote0 "·" NilR
  quote (ConsR ty ctx) = quote2 "," ConsR ty ctx

  unifyVal _ NilR NilR = pure ()
  unifyVal unif (ConsR ty ctx) (ConsR ty' ctx') = unif ty ty' *> unif ctx ctx'
  unifyVal _ _ _ = empty

  derefVal _ NilR = pure Nil
  derefVal deref (ConsR ty ctx) = Cons <$> deref ty <*> deref ctx

nil :: Logic Ctx var
nil = Ground NilR

cons :: Logic Ty var -> Logic Ctx var -> Logic Ctx var
cons ty ctx = Ground $ ConsR ty ctx

-- Moded
nilM :: T '[] Ctx rel
nilM = ground nil

consM :: T vs1 Ty rel -> T vs2 Ctx rel -> T (Union vs1 vs2) Ctx rel
consM = lift2 cons

--------------------------------------------------------------------------------
-- Mode-checked lookup: Γ(n) = A
-- Modes: I, I, O
--------------------------------------------------------------------------------

lookupM :: (Redex rel, LogicType Ctx, LogicType Nat, LogicType Ty)
        => T vs1 Ctx rel -> T vs2 Nat rel -> T vs3 Ty rel
        -> AppliedM rel "lookup" '[I, I, O] '[vs1, vs2, vs3] '[Ctx, Nat, Ty]
lookupM = mjudge3 (I :* I :* O :* MNil)
  [ ruleM @"lookup" "lookup-here" $ R.do
      ty   <- fresh
      rest <- fresh
      -- concl grounds: ctx (via consM ty rest), n (via zroM)
      -- concl produces: ty (O position)
      R.concl $ lookupM (consM ty rest) zroM ty

  , ruleM @"lookup" "lookup-there" $ R.do
      ty'  <- fresh
      rest <- fresh
      n'   <- fresh
      ty   <- fresh
      -- concl grounds: ctx, n (via sucM n')
      -- prem requires: rest (from concl via consM), n' (from concl via sucM)
      -- prem produces: ty
      R.concl $ lookupM (consM ty' rest) (sucM n') ty
      R.prem $ lookupM rest n' ty
  ]

--------------------------------------------------------------------------------
-- Mode-checked synthesis: Γ ⊢ e ⇒ A
-- Modes: I, I, O
--------------------------------------------------------------------------------

synthM :: (Redex rel, LogicType Ctx, LogicType Tm, LogicType Ty)
       => T vs1 Ctx rel -> T vs2 Tm rel -> T vs3 Ty rel
       -> AppliedM rel "synth" '[I, I, O] '[vs1, vs2, vs3] '[Ctx, Tm, Ty]
synthM = mjudge3 (I :* I :* O :* MNil)
  [ -- ⇒Var: Γ(x) = A  ⟹  Γ ⊢ x ⇒ A
    ruleM @"synth" "⇒Var" $ R.do
      ctx <- fresh
      n   <- fresh
      ty  <- fresh
      R.concl $ synthM ctx (varM n) ty
      R.prem $ lookupM ctx n ty

  , -- ⇒Unit: Γ ⊢ () ⇒ Unit
    ruleM @"synth" "⇒Unit" $ R.do
      ctx <- fresh
      R.concl $ synthM ctx unitM tunitM

  , -- ⇒λ:: Γ,A ⊢ e ⇒ B  ⟹  Γ ⊢ λx:A.e ⇒ A→B
    ruleM @"synth" "⇒λ:" $ R.do
      ctx  <- fresh
      a    <- fresh
      b    <- fresh
      body <- fresh
      R.concl $ synthM ctx (lamAnnM a body) (tarrM a b)
      R.prem $ synthM (consM a ctx) body b

  , -- ⇒App: Γ ⊢ e1 ⇒ A→B  ∧  Γ ⊢ e2 ⇐ A  ⟹  Γ ⊢ e1 e2 ⇒ B
    ruleM @"synth" "⇒App" $ R.do
      ctx <- fresh
      e1  <- fresh
      e2  <- fresh
      a   <- fresh
      b   <- fresh
      R.concl $ synthM ctx (appM e1 e2) b
      R.prem $ synthM ctx e1 (tarrM a b)
      R.prem $ checkM ctx e2 a

  , -- ⇒Ann: Γ ⊢ e ⇐ A  ⟹  Γ ⊢ (e:A) ⇒ A
    ruleM @"synth" "⇒Ann" $ R.do
      ctx <- fresh
      e   <- fresh
      ty  <- fresh
      R.concl $ synthM ctx (annM e ty) ty
      R.prem $ checkM ctx e ty
  ]

--------------------------------------------------------------------------------
-- Mode-checked checking: Γ ⊢ e ⇐ A
-- Modes: I, I, I
--------------------------------------------------------------------------------

checkM :: (Redex rel, LogicType Ctx, LogicType Tm, LogicType Ty)
       => T vs1 Ctx rel -> T vs2 Tm rel -> T vs3 Ty rel
       -> AppliedM rel "check" '[I, I, I] '[vs1, vs2, vs3] '[Ctx, Tm, Ty]
checkM = mjudge3 (I :* I :* I :* MNil)
  [ -- ⇐λ: Γ,A ⊢ e ⇐ B  ⟹  Γ ⊢ λx.e ⇐ A→B
    ruleM @"check" "⇐λ" $ R.do
      ctx  <- fresh
      a    <- fresh
      b    <- fresh
      body <- fresh
      R.concl $ checkM ctx (lamM body) (tarrM a b)
      R.prem $ checkM (consM a ctx) body b

  , -- ⇐Sub: Γ ⊢ e ⇒ A  ⟹  Γ ⊢ e ⇐ A
    ruleM @"check" "⇐Sub" $ R.do
      ctx <- fresh
      e   <- fresh
      ty  <- fresh
      R.concl $ checkM ctx e ty
      R.prem $ synthM ctx e ty
  ]

--------------------------------------------------------------------------------
-- Running queries
--------------------------------------------------------------------------------

synthIO :: Ctx -> Tm -> Stream Ty
synthIO ctx0 e0 = runSubstRedex $ F.fresh $ \ty -> do
  let ctxL = Ground $ project ctx0
      eL   = Ground $ project e0
  -- Run the moded judgment
  appGoal $ toApplied $ synthM (T ctxL) (T eL) (T ty)
  eval ty

checkIII :: Ctx -> Tm -> Ty -> Stream ()
checkIII ctx0 e0 ty0 = runSubstRedex $ do
  let ctxL = Ground $ project ctx0
      eL   = Ground $ project e0
      tyL  = Ground $ project ty0
  appGoal $ toApplied $ checkM (T ctxL) (T eL) (T tyL)
  pure ()

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "=== Mode-Checked Bidirectional STLC ==="
  putStrLn ""

  -- Example 1: Synthesize λx:Unit. x
  let ex1 = LamAnn TUnit (Var Z)
  putStrLn "1. Synthesize λx:Unit. x"
  print $ takeS 1 (synthIO Nil ex1)
  putStrLn ""

  -- Example 2: Synthesize ((λx. x) : Unit → Unit)
  let ex2 = Ann (Lam (Var Z)) (TArr TUnit TUnit)
  putStrLn "2. Synthesize ((λx. x) : Unit → Unit)"
  print $ takeS 1 (synthIO Nil ex2)
  putStrLn ""

  -- Example 3: Check λx. x ⇐ Unit → Unit
  let ex3 = Lam (Var Z)
  putStrLn "3. Check λx. x ⇐ Unit → Unit"
  print $ takeS 1 (checkIII Nil ex3 (TArr TUnit TUnit))
  putStrLn ""

  -- Example 4: Application
  let ex4 = App (Ann (Lam (Var Z)) (TArr TUnit TUnit)) Unit
  putStrLn "4. Synthesize ((λx. x) : Unit → Unit) ()"
  print $ takeS 1 (synthIO Nil ex4)
  putStrLn ""

  putStrLn "=== Mode Checking Guarantee ==="
  putStrLn ""
  putStrLn "All rules above compile, which proves that:"
  putStrLn "  - lookup (I,I,O): ctx and index ground → type output"
  putStrLn "  - synth (I,I,O): ctx and term ground → type output"
  putStrLn "  - check (I,I,I): all positions ground (verification)"
  putStrLn ""
  putStrLn "If you tried to write an ill-moded rule like:"
  putStrLn "  prem synthM (ctx :! e :! ty :! ANil)"
  putStrLn "  concl synthM (ctx :! e :! ty' :! ANil)  -- ty' not grounded!"
  putStrLn "It would fail at compile time with:"
  putStrLn "  Mode error in \"synth\":"
  putStrLn "    grounded: '[...]"
  putStrLn "    blocked: synth needs '[ty']"
