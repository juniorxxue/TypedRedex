{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Main (main) where

import Control.Applicative (empty)
import Shallow.Core.Kanren
import Shallow.Core.Internal.Logic (Logic (Ground), LogicType (..))
import Shallow.Interpreters.SubstKanren (runSubstKanren, takeS, Stream)
import Shallow.Interpreters.TracingKanren (runWithDerivation, prettyDerivation, Derivation(..))
import Shallow.Utils.Rule
import Shallow.Utils.Type (quote0, quote1, quote2)

-- Bidirectional typing for STLC (Dunfield & Krishnaswami style)
-- Using inference-rule style syntax
--
-- Synthesis: Γ ⊢ e ⇒ A
-- Checking:  Γ ⊢ e ⇐ A

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

unit :: Logic Tm var
unit = Ground UnitR

lam :: Logic Tm var -> Logic Tm var
lam = Ground . LamR

lamAnn :: Logic Ty var -> Logic Tm var -> Logic Tm var
lamAnn ty b = Ground $ LamAnnR ty b

app :: Logic Tm var -> Logic Tm var -> Logic Tm var
app f a = Ground $ AppR f a

ann :: Logic Tm var -> Logic Ty var -> Logic Tm var
ann e ty = Ground $ AnnR e ty

--------------------------------------------------------------------------------
-- Type contexts as lists (reversed, so head = most recent binding)
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

--------------------------------------------------------------------------------
-- Context lookup: Γ(n) = A
--------------------------------------------------------------------------------

-- Base case: (Γ, A)(0) = A
--
-- ─────────────────────── [lookup-here]
-- lookup (Γ,A) 0 A

lookupHere :: (Kanren rel) => L Ctx rel -> L Nat rel -> L Ty rel -> Relation rel
lookupHere = rule3 "lookup-here" $ \concl ->
  fresh2 $ \ty rest ->
    concl (cons ty rest) zro ty

-- Inductive: (Γ, B)(S n) = A  ←  Γ(n) = A
--
--      lookup Γ n A
-- ─────────────────────── [lookup-there]
-- lookup (Γ,B) (S n) A

lookupThere :: (Kanren rel) => L Ctx rel -> L Nat rel -> L Ty rel -> Relation rel
lookupThere = rule3 "lookup-there" $ \concl ->
  fresh4 $ \ty' rest n' ty -> do
    concl (cons ty' rest) (suc n') ty
    call $ lookup' rest n' ty

-- Combined lookup relation
lookup' :: (Kanren rel) => L Ctx rel -> L Nat rel -> L Ty rel -> Relation rel
lookup' = rules3 "lookup"
  [ lookupHere
  , lookupThere
  ]

--------------------------------------------------------------------------------
-- Synthesis mode: Γ ⊢ e ⇒ A
--------------------------------------------------------------------------------

-- Variable rule:
--      Γ(x) = A
-- ─────────────────── [⇒Var]
--   Γ ⊢ x ⇒ A

synthVar :: (Kanren rel) => L Ctx rel -> L Tm rel -> L Ty rel -> Relation rel
synthVar = rule3 "⇒Var" $ \concl ->
  fresh3 $ \ctx n ty -> do
    concl ctx (var n) ty
    call $ lookup' ctx n ty

-- Unit rule:
-- ─────────────────── [⇒Unit]
--   Γ ⊢ () ⇒ Unit

synthUnit :: (Kanren rel) => L Ctx rel -> L Tm rel -> L Ty rel -> Relation rel
synthUnit = rule3 "⇒Unit" $ \concl ->
  fresh $ \ctx ->
    concl ctx unit tunit

-- Annotated lambda rule:
--   Γ, x:A ⊢ e ⇒ B
-- ─────────────────────── [⇒λ:]
--   Γ ⊢ (λx:A.e) ⇒ A → B

synthLamAnn :: (Kanren rel) => L Ctx rel -> L Tm rel -> L Ty rel -> Relation rel
synthLamAnn = rule3 "⇒λ:" $ \concl ->
  fresh4 $ \ctx a b body -> do
    concl ctx (lamAnn a body) (tarr a b)
    call $ synth (cons a ctx) body b

-- Application rule:
--   Γ ⊢ e₁ ⇒ A → B    Γ ⊢ e₂ ⇐ A
-- ─────────────────────────────────── [⇒App]
--        Γ ⊢ e₁ e₂ ⇒ B

synthApp :: (Kanren rel) => L Ctx rel -> L Tm rel -> L Ty rel -> Relation rel
synthApp = rule3 "⇒App" $ \concl ->
  fresh5 $ \ctx e1 e2 a b -> do
    concl ctx (app e1 e2) b
    call $ synth ctx e1 (tarr a b)
    call $ check ctx e2 a

-- Annotation rule:
--      Γ ⊢ e ⇐ A
-- ─────────────────── [⇒Ann]
--   Γ ⊢ (e:A) ⇒ A

synthAnn :: (Kanren rel) => L Ctx rel -> L Tm rel -> L Ty rel -> Relation rel
synthAnn = rule3 "⇒Ann" $ \concl ->
  fresh3 $ \ctx e ty -> do
    concl ctx (ann e ty) ty
    call $ check ctx e ty

-- Combined synthesis relation
synth :: (Kanren rel) => L Ctx rel -> L Tm rel -> L Ty rel -> Relation rel
synth = rules3 "synth"
  [ synthVar
  , synthUnit
  , synthLamAnn
  , synthApp
  , synthAnn
  ]

--------------------------------------------------------------------------------
-- Checking mode: Γ ⊢ e ⇐ A
--------------------------------------------------------------------------------

-- Lambda introduction (checking):
--   Γ, x:A ⊢ e ⇐ B
-- ─────────────────── [⇐λ]
--   Γ ⊢ λx.e ⇐ A → B

checkLam :: (Kanren rel) => L Ctx rel -> L Tm rel -> L Ty rel -> Relation rel
checkLam = rule3 "⇐λ" $ \concl ->
  fresh4 $ \ctx a b body -> do
    concl ctx (lam body) (tarr a b)
    call $ check (cons a ctx) body b

-- Subsumption rule (checking falls back to synthesis):
--      Γ ⊢ e ⇒ A
-- ─────────────────── [⇐Sub]
--      Γ ⊢ e ⇐ A

checkSub :: (Kanren rel) => L Ctx rel -> L Tm rel -> L Ty rel -> Relation rel
checkSub = rule3 "⇐Sub" $ \concl ->
  fresh3 $ \ctx e ty -> do
    concl ctx e ty
    call $ synth ctx e ty

-- Combined checking relation
check :: (Kanren rel) => L Ctx rel -> L Tm rel -> L Ty rel -> Relation rel
check = rules3 "check"
  [ checkLam
  , checkSub
  ]

--------------------------------------------------------------------------------
-- Running queries
--------------------------------------------------------------------------------

-- Run synthesis in mode (I,I,O): given ctx and term, find type
synthIO :: Ctx -> Tm -> Stream Ty
synthIO ctx0 e0 = runSubstKanren $ fresh $ \ty -> do
  _ <- embed $ synth (Ground $ project ctx0) (Ground $ project e0) ty
  eval ty

-- Run checking in mode (I,I,I): given ctx, term, and type, verify
checkIII :: Ctx -> Tm -> Ty -> Stream ()
checkIII ctx0 e0 ty0 = runSubstKanren $ do
  _ <- embed $ check (Ground $ project ctx0) (Ground $ project e0) (Ground $ project ty0)
  pure ()

-- Run synthesis with derivation tracing
synthWithTrace :: Ctx -> Tm -> Stream (Ty, Derivation)
synthWithTrace ctx0 e0 = runWithDerivation $ fresh $ \ty -> do
  _ <- embed $ synth (Ground $ project ctx0) (Ground $ project e0) ty
  eval ty

-- Run checking with derivation tracing
checkWithTrace :: Ctx -> Tm -> Ty -> Stream ((), Derivation)
checkWithTrace ctx0 e0 ty0 = runWithDerivation $ do
  _ <- embed $ check (Ground $ project ctx0) (Ground $ project e0) (Ground $ project ty0)
  pure ()

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "=== Bidirectional Typing for STLC ==="
  putStrLn ""

  -- Example 1: Synthesize type for (λx:Unit. x)
  let ex1 = LamAnn TUnit (Var Z)
  putStrLn "Example 1: Synthesize λx:Unit. x"
  print $ takeS 1 (synthIO Nil ex1)
  putStrLn ""

  -- Example 2: Synthesize type for annotated identity
  let ex2 = Ann (Lam (Var Z)) (TArr TUnit TUnit)
  putStrLn "Example 2: Synthesize ((λx. x) : Unit → Unit)"
  print $ takeS 1 (synthIO Nil ex2)
  putStrLn ""

  -- Example 3: Check that (λx. x) has type Unit → Unit
  let ex3 = Lam (Var Z)
  putStrLn "Example 3: Check λx. x ⇐ Unit → Unit"
  print $ takeS 1 (checkIII Nil ex3 (TArr TUnit TUnit))
  putStrLn ""

  -- Example 4: Application
  let ex4 = App (Ann (Lam (Var Z)) (TArr TUnit TUnit)) Unit
  putStrLn "Example 4: Synthesize ((λx. x) : Unit → Unit) ()"
  print $ takeS 1 (synthIO Nil ex4)
  putStrLn ""

  putStrLn "=== Derivation Trees ==="
  putStrLn ""

  -- (λf:Unit→Unit. λx:Unit. f x) ⇒ (Unit→Unit) → Unit → Unit
  let ex5 = LamAnn (TArr TUnit TUnit) (LamAnn TUnit (App (Var (S Z)) (Var Z)))
  putStrLn "Derivation 5: λf:Unit→Unit. λx:Unit. f x"
  putStrLn "Expected: Nested ⇒λ: with ⇒App, lookup"
  case takeS 1 (synthWithTrace Nil ex5) of
    [(ty, deriv)] -> do
      putStrLn $ "Type: " ++ show ty
      putStrLn $ prettyDerivation deriv
    _ -> putStrLn "No derivation found"
