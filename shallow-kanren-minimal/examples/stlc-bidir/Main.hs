{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Main (main) where

import Control.Applicative (empty)
import Shallow.Core.Kanren
import Shallow.Core.Internal.Logic (Logic (Ground), LogicType (..))
import Shallow.Interpreters.SubstKanren (runSubstKanren, takeS, Stream)
import Shallow.Utils.Type (quote0, quote1, quote2)

-- Bidirectional typing for STLC (Dunfield & Krishnaswami style)
-- Uses de Bruijn indices for variables

-- Natural numbers for de Bruijn indices
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

-- Types
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

  quote TUnitR = quote0 "TUnit" TUnitR
  quote (TArrR a b) = quote2 "TArr" TArrR a b

  unifyVal _ TUnitR TUnitR = pure ()
  unifyVal unif (TArrR a b) (TArrR a' b') = unif a a' *> unif b b'
  unifyVal _ _ _ = empty

  derefVal _ TUnitR = pure TUnit
  derefVal deref (TArrR a b) = TArr <$> deref a <*> deref b

tunit :: Logic Ty var
tunit = Ground TUnitR

tarr :: Logic Ty var -> Logic Ty var -> Logic Ty var
tarr a b = Ground $ TArrR a b

-- Terms
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
  quote UnitR = quote0 "Unit" UnitR
  quote (LamR b) = quote1 "Lam" LamR b
  quote (LamAnnR ty b) = quote2 "LamAnn" LamAnnR ty b
  quote (AppR f a) = quote2 "App" AppR f a
  quote (AnnR e ty) = quote2 "Ann" AnnR e ty

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

-- Type contexts as lists (reversed, so head = most recent binding)
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

  quote NilR = quote0 "Nil" NilR
  quote (ConsR ty ctx) = quote2 "Cons" ConsR ty ctx

  unifyVal _ NilR NilR = pure ()
  unifyVal unif (ConsR ty ctx) (ConsR ty' ctx') = unif ty ty' *> unif ctx ctx'
  unifyVal _ _ _ = empty

  derefVal _ NilR = pure Nil
  derefVal deref (ConsR ty ctx) = Cons <$> deref ty <*> deref ctx

nil :: Logic Ctx var
nil = Ground NilR

cons :: Logic Ty var -> Logic Ctx var -> Logic Ctx var
cons ty ctx = Ground $ ConsR ty ctx

-- Context lookup: lookup ctx n ty means ctx(n) = ty
lookup' :: (Kanren rel) => L Ctx rel -> L Nat rel -> L Ty rel -> Relation rel
lookup' = relation3 "lookup" $ \ctx n ty ->
  conde
    [ -- Base case: lookup (Cons ty _) Z ty
      fresh $ \rest -> do
        n <=> zro
        ctx <=> cons ty rest
        pure ()
    , -- Inductive: lookup (Cons _ ctx') (S n') ty  ← lookup ctx' n' ty
      fresh3 $ \ty' rest n' -> do
        n <=> suc n'
        ctx <=> cons ty' rest
        call $ lookup' rest n' ty
        pure ()
    ]

-- Bidirectional typing
-- Synthesis mode: synth Γ e A means Γ ⊢ e ⇒ A
synth :: (Kanren rel) => L Ctx rel -> L Tm rel -> L Ty rel -> Relation rel
synth = relation3 "synth" $ \ctx e ty ->
  conde
    [ -- Var: Γ ⊢ x ⇒ A  if Γ(x) = A
      fresh $ \n -> do
        e <=> var n
        call $ lookup' ctx n ty
        pure ()
    , -- Unit: Γ ⊢ () ⇒ Unit
      do
        e <=> unit
        ty <=> tunit
        pure ()
    , -- →I⇒: Γ, x:A ⊢ e ⇒ B  =>  Γ ⊢ (λx:A.e) ⇒ A → B
      fresh3 $ \a b body -> do
        e <=> lamAnn a body
        ty <=> tarr a b
        call $ synth (cons a ctx) body b
        pure ()
    , -- →E: Γ ⊢ e₁ ⇒ A → B   Γ ⊢ e₂ ⇐ A  =>  Γ ⊢ e₁ e₂ ⇒ B
      fresh3 $ \e1 e2 a -> do
        e <=> app e1 e2
        call $ synth ctx e1 (tarr a ty)
        call $ check ctx e2 a
        pure ()
    , -- Anno: Γ ⊢ e ⇐ A  =>  Γ ⊢ (e:A) ⇒ A
      fresh $ \e' -> do
        e <=> ann e' ty
        call $ check ctx e' ty
        pure ()
    ]

-- Checking mode: check Γ e A means Γ ⊢ e ⇐ A
check :: (Kanren rel) => L Ctx rel -> L Tm rel -> L Ty rel -> Relation rel
check = relation3 "check" $ \ctx e ty ->
  conde
    [ -- →I⇐: Γ, x:A ⊢ e ⇐ B  =>  Γ ⊢ λx.e ⇐ A → B
      fresh3 $ \a b body -> do
        e <=> lam body
        ty <=> tarr a b
        call $ check (cons a ctx) body b
        pure ()
    , -- Sub: Γ ⊢ e ⇒ A   A = B  =>  Γ ⊢ e ⇐ B
      -- (unification handles the equality check)
      call $ synth ctx e ty
    ]

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

main :: IO ()
main = do
  putStrLn "=== Bidirectional Typing for STLC ==="
  putStrLn ""

  -- Example 1: Synthesize type for (λx:Unit. x)
  let id_unit = LamAnn TUnit (Var Z)
  putStrLn $ "Synthesize: λx:Unit. x"
  print $ takeS 1 (synthIO Nil id_unit)
  putStrLn ""

  -- Example 2: Synthesize type for annotated identity
  let id_ann = Ann (Lam (Var Z)) (TArr TUnit TUnit)
  putStrLn $ "Synthesize: ((λx. x) : Unit → Unit)"
  print $ takeS 1 (synthIO Nil id_ann)
  putStrLn ""

  -- Example 3: Check that (λx. x) has type Unit → Unit
  let id_unannotated = Lam (Var Z)
  putStrLn $ "Check: λx. x ⇐ Unit → Unit"
  print $ takeS 1 (checkIII Nil id_unannotated (TArr TUnit TUnit))
  putStrLn ""

  -- Example 4: Application
  let app_term = App (Ann (Lam (Var Z)) (TArr TUnit TUnit)) Unit
  putStrLn $ "Synthesize: ((λx. x) : Unit → Unit) ()"
  print $ takeS 1 (synthIO Nil app_term)
  putStrLn ""

  -- Example 5: Term synthesis
  -- Given type (Unit → Unit) → Unit, synthesize a term
  putStrLn $ "Synthesize term with type (Unit → Unit) → Unit"
  let query = runSubstKanren $ fresh $ \e -> do
        _ <- embed $ synth nil e (tarr (tarr tunit tunit) tunit)
        eval e
  print $ takeS 3 query
