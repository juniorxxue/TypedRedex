{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE DataKinds #-}

module Main (main) where

import Control.Applicative (empty)
import TypedRedex
import TypedRedex.Core.Internal.Logic (Logic (Ground), LogicType (..))
import TypedRedex.Interp.Subst (runSubstRedex, takeS, Stream)
import TypedRedex.Interp.Tracing (runWithDerivation, runWithDerivationWith, prettyDerivationWith, Derivation(..), JudgmentFormatter(..), defaultFormatConclusion)
import TypedRedex.Interp.Format (TermFormatter(..), subscriptNum)
import TypedRedex.DSL.Type (quote0, quote1, quote2)

-- Bidirectional typing for STLC (Dunfield & Krishnaswami style)
-- Using the new judgment/rule syntax
--
-- Synthesis: Γ ⊢ e ⇒ A
-- Checking:  Γ ⊢ e ⇐ A

--------------------------------------------------------------------------------
-- Judgment Formatter for Bidirectional STLC
--------------------------------------------------------------------------------

-- | Custom formatter for bidirectional typing derivations
data BidirFormatter = BidirFormatter

instance JudgmentFormatter BidirFormatter where
  formatJudgment _ name args = case (name, args) of
    -- Synthesis rules (start with ⇒)
    (n, [ctx, e, ty]) | isSynthRule n -> ctx ++ " ⊢ " ++ e ++ " ⇒ " ++ ty
    -- Checking rules (start with ⇐)
    (n, [ctx, e, ty]) | isCheckRule n -> ctx ++ " ⊢ " ++ e ++ " ⇐ " ++ ty
    -- Context lookup
    (n, [ctx, idx, ty]) | isLookupRule n -> ctx ++ "(" ++ idx ++ ") = " ++ ty
    -- Default
    _ -> defaultFormatConclusion name args
    where
      isSynthRule ('⇒':_) = True
      isSynthRule s = "synth" `isPrefixOf` s
      isCheckRule ('⇐':_) = True
      isCheckRule s = "check" `isPrefixOf` s
      isLookupRule s = "lookup" `isPrefixOf` s
      isPrefixOf [] _ = True
      isPrefixOf _ [] = False
      isPrefixOf (x:xs) (y:ys) = x == y && isPrefixOf xs ys

-- | TermFormatter for nice term display
instance TermFormatter BidirFormatter where
  formatTerm _ name args = case (name, args) of
    -- Application
    ("App", [f, a]) -> Just $ "(" ++ f ++ " " ++ a ++ ")"
    -- Lambda (unannotated)
    ("λ", [b]) -> Just $ "(λ." ++ b ++ ")"
    -- Lambda (annotated)
    ("λ:", [ty, b]) -> Just $ "(λ:" ++ ty ++ ". " ++ b ++ ")"
    -- Annotation
    (":", [e, ty]) -> Just $ "(" ++ e ++ " : " ++ ty ++ ")"
    -- Variables
    ("Var", [n]) -> Just $ parseAndShowVar n
    -- Unit
    ("()", []) -> Just "()"
    -- Types
    ("Unit", []) -> Just "Unit"
    ("→", [a, b]) -> Just $ "(" ++ a ++ " → " ++ b ++ ")"
    -- Contexts
    ("·", []) -> Just "·"
    (",", [ty, ctx]) -> Just $ ctx ++ ", " ++ ty
    -- Naturals
    ("Z", []) -> Just "0"
    ("S", [n]) -> Just $ "S(" ++ n ++ ")"
    _ -> Nothing
    where
      parseAndShowVar n = case parseNat n of
        Just k  -> "x" ++ subscriptNum (show k)
        Nothing -> n
      parseNat "0" = Just 0
      parseNat ('S':'(':rest) = case parseNat (init rest) of
        Just k -> Just (k + 1)
        Nothing -> Nothing
      parseNat s | all isDigit s = Just (read s)
      parseNat _ = Nothing
      isDigit c = c `elem` "0123456789"

-- | Pretty-print derivation with bidirectional typing formatting
prettyDerivation :: Derivation -> String
prettyDerivation = prettyDerivationWith BidirFormatter

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
-- Context lookup: Γ(n) = A (using judgment/rule style)
--------------------------------------------------------------------------------

-- ─────────────────────── [lookup-here]
-- lookup (Γ,A) 0 A
--
--      lookup Γ n A
-- ─────────────────────── [lookup-there]
-- lookup (Γ,B) (S n) A

lookup' :: (Redex rel) => Judge rel '[Ctx, Nat, Ty]
lookup' = judgment "lookup" [lookupHere, lookupThere]
  where
    lookupHere = rule "lookup-here" $ fresh2 $ \ty rest ->
      concl $ lookup' (cons ty rest) zro ty

    lookupThere = rule "lookup-there" $ fresh4 $ \ty' rest n' ty -> do
      concl $ lookup' (cons ty' rest) (suc n') ty
      prem  $ lookup' rest n' ty

--------------------------------------------------------------------------------
-- Synthesis mode: Γ ⊢ e ⇒ A (using judgment/rule style)
--------------------------------------------------------------------------------

-- Variable rule:
--      Γ(x) = A
-- ─────────────────── [⇒Var]
--   Γ ⊢ x ⇒ A
--
-- Unit rule:
-- ─────────────────── [⇒Unit]
--   Γ ⊢ () ⇒ Unit
--
-- Annotated lambda rule:
--   Γ, x:A ⊢ e ⇒ B
-- ─────────────────────── [⇒λ:]
--   Γ ⊢ (λx:A.e) ⇒ A → B
--
-- Application rule:
--   Γ ⊢ e₁ ⇒ A → B    Γ ⊢ e₂ ⇐ A
-- ─────────────────────────────────── [⇒App]
--        Γ ⊢ e₁ e₂ ⇒ B
--
-- Annotation rule:
--      Γ ⊢ e ⇐ A
-- ─────────────────── [⇒Ann]
--   Γ ⊢ (e:A) ⇒ A

synth :: (Redex rel) => Judge rel '[Ctx, Tm, Ty]
synth = judgment "synth" [synthVar, synthUnit, synthLamAnn, synthApp, synthAnn]
  where
    synthVar = rule "⇒Var" $ fresh3 $ \ctx n ty -> do
      concl $ synth ctx (var n) ty
      prem  $ lookup' ctx n ty

    synthUnit = rule "⇒Unit" $ fresh $ \ctx ->
      concl $ synth ctx unit tunit

    synthLamAnn = rule "⇒λ:" $ fresh4 $ \ctx a b body -> do
      concl $ synth ctx (lamAnn a body) (tarr a b)
      prem  $ synth (cons a ctx) body b

    synthApp = rule "⇒App" $ fresh5 $ \ctx e1 e2 a b -> do
      concl $ synth ctx (app e1 e2) b
      prem  $ synth ctx e1 (tarr a b)
      prem  $ check ctx e2 a

    synthAnn = rule "⇒Ann" $ fresh3 $ \ctx e ty -> do
      concl $ synth ctx (ann e ty) ty
      prem  $ check ctx e ty

--------------------------------------------------------------------------------
-- Checking mode: Γ ⊢ e ⇐ A (using judgment/rule style)
--------------------------------------------------------------------------------

-- Lambda introduction (checking):
--   Γ, x:A ⊢ e ⇐ B
-- ─────────────────── [⇐λ]
--   Γ ⊢ λx.e ⇐ A → B
--
-- Subsumption rule (checking falls back to synthesis):
--      Γ ⊢ e ⇒ A
-- ─────────────────── [⇐Sub]
--      Γ ⊢ e ⇐ A

check :: (Redex rel) => Judge rel '[Ctx, Tm, Ty]
check = judgment "check" [checkLam, checkSub]
  where
    checkLam = rule "⇐λ" $ fresh4 $ \ctx a b body -> do
      concl $ check ctx (lam body) (tarr a b)
      prem  $ check (cons a ctx) body b

    checkSub = rule "⇐Sub" $ fresh3 $ \ctx e ty -> do
      concl $ check ctx e ty
      prem  $ synth ctx e ty

--------------------------------------------------------------------------------
-- Running queries
--------------------------------------------------------------------------------

-- Run synthesis in mode (I,I,O): given ctx and term, find type
synthIO :: Ctx -> Tm -> Stream Ty
synthIO ctx0 e0 = runSubstRedex $ fresh $ \ty -> do
  appGoal $ synth (Ground $ project ctx0) (Ground $ project e0) ty
  eval ty

-- Run checking in mode (I,I,I): given ctx, term, and type, verify
checkIII :: Ctx -> Tm -> Ty -> Stream ()
checkIII ctx0 e0 ty0 = runSubstRedex $ do
  appGoal $ check (Ground $ project ctx0) (Ground $ project e0) (Ground $ project ty0)
  pure ()

-- Run synthesis with derivation tracing using custom formatter
synthWithTrace :: Ctx -> Tm -> Stream (Ty, Derivation)
synthWithTrace ctx0 e0 = runWithDerivationWith BidirFormatter $ fresh $ \ty -> do
  appGoal $ synth (Ground $ project ctx0) (Ground $ project e0) ty
  eval ty

-- Run checking with derivation tracing using custom formatter
checkWithTrace :: Ctx -> Tm -> Ty -> Stream ((), Derivation)
checkWithTrace ctx0 e0 ty0 = runWithDerivationWith BidirFormatter $ do
  appGoal $ check (Ground $ project ctx0) (Ground $ project e0) (Ground $ project ty0)
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
