{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Main (main) where

import Control.Applicative (empty)
import TypedRedex.Core.Redex
import TypedRedex.Core.Internal.Logic (Logic (Ground), LogicType (..))
import TypedRedex.Interpreters.SubstRedex (runSubstRedex, takeS, Stream)
import TypedRedex.Utils.Type (quote0, quote1, quote2)

-- Hindley-Milner Type Inference
-- Simplified version without polymorphism (Algorithm W style)

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

-- Types: monotypes only (no ∀ for simplicity)
-- In a real HM system, type variables would be handled via logic variables
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
  = Var Nat
  | Unit
  | Lam Tm
  | App Tm Tm
  | Let Tm Tm  -- let x = e1 in e2 (de Bruijn)
  deriving (Eq, Show)

instance LogicType Tm where
  data Reified Tm var
    = VarR (Logic Nat var)
    | UnitR
    | LamR (Logic Tm var)
    | AppR (Logic Tm var) (Logic Tm var)
    | LetR (Logic Tm var) (Logic Tm var)

  project (Var n) = VarR (Ground $ project n)
  project Unit = UnitR
  project (Lam b) = LamR (Ground $ project b)
  project (App f a) = AppR (Ground $ project f) (Ground $ project a)
  project (Let e1 e2) = LetR (Ground $ project e1) (Ground $ project e2)

  reify (VarR (Ground n)) = Var <$> reify n
  reify UnitR = Just Unit
  reify (LamR (Ground b)) = Lam <$> reify b
  reify (AppR (Ground f) (Ground a)) = App <$> reify f <*> reify a
  reify (LetR (Ground e1) (Ground e2)) = Let <$> reify e1 <*> reify e2
  reify _ = Nothing

  quote (VarR n) = quote1 "Var" VarR n
  quote UnitR = quote0 "Unit" UnitR
  quote (LamR b) = quote1 "Lam" LamR b
  quote (AppR f a) = quote2 "App" AppR f a
  quote (LetR e1 e2) = quote2 "Let" LetR e1 e2

  unifyVal unif (VarR n) (VarR n') = unif n n'
  unifyVal _ UnitR UnitR = pure ()
  unifyVal unif (LamR b) (LamR b') = unif b b'
  unifyVal unif (AppR f a) (AppR f' a') = unif f f' *> unif a a'
  unifyVal unif (LetR e1 e2) (LetR e1' e2') = unif e1 e1' *> unif e2 e2'
  unifyVal _ _ _ = empty

  derefVal deref (VarR n) = Var <$> deref n
  derefVal _ UnitR = pure Unit
  derefVal deref (LamR b) = Lam <$> deref b
  derefVal deref (AppR f a) = App <$> deref f <*> deref a
  derefVal deref (LetR e1 e2) = Let <$> deref e1 <*> deref e2

var :: Logic Nat var -> Logic Tm var
var = Ground . VarR

unit :: Logic Tm var
unit = Ground UnitR

lam :: Logic Tm var -> Logic Tm var
lam = Ground . LamR

app :: Logic Tm var -> Logic Tm var -> Logic Tm var
app f a = Ground $ AppR f a

letIn :: Logic Tm var -> Logic Tm var -> Logic Tm var
letIn e1 e2 = Ground $ LetR e1 e2

-- Type environments
data Env = ENil | ECons Ty Env deriving (Eq, Show)

instance LogicType Env where
  data Reified Env var
    = ENilR
    | EConsR (Logic Ty var) (Logic Env var)

  project ENil = ENilR
  project (ECons ty env) = EConsR (Ground $ project ty) (Ground $ project env)

  reify ENilR = Just ENil
  reify (EConsR (Ground ty) (Ground env)) = ECons <$> reify ty <*> reify env
  reify _ = Nothing

  quote ENilR = quote0 "ENil" ENilR
  quote (EConsR ty env) = quote2 "ECons" EConsR ty env

  unifyVal _ ENilR ENilR = pure ()
  unifyVal unif (EConsR ty env) (EConsR ty' env') = unif ty ty' *> unif env env'
  unifyVal _ _ _ = empty

  derefVal _ ENilR = pure ENil
  derefVal deref (EConsR ty env) = ECons <$> deref ty <*> deref env

enil :: Logic Env var
enil = Ground ENilR

econs :: Logic Ty var -> Logic Env var -> Logic Env var
econs ty env = Ground $ EConsR ty env

-- Environment lookup
lookupEnv :: (Redex rel) => L Env rel -> L Nat rel -> L Ty rel -> Relation rel
lookupEnv = relation3 "lookupEnv" $ \env n ty ->
  conde
    [ fresh $ \rest -> do
        n <=> zro
        env <=> econs ty rest
        pure ()
    , fresh3 $ \ty' rest n' -> do
        n <=> suc n'
        env <=> econs ty' rest
        call $ lookupEnv rest n' ty
        pure ()
    ]

-- Type inference relation: infer Γ e A means Γ ⊢ e : A
infer :: (Redex rel) => L Env rel -> L Tm rel -> L Ty rel -> Relation rel
infer = relation3 "infer" $ \env e ty ->
  conde
    [ -- Var: Γ ⊢ x : A  if Γ(x) = A
      fresh $ \n -> do
        e <=> var n
        call $ lookupEnv env n ty
        pure ()
    , -- Unit: Γ ⊢ () : Unit
      do
        e <=> unit
        ty <=> tunit
        pure ()
    , -- Lam: Γ, x:A ⊢ e : B  =>  Γ ⊢ λx.e : A → B
      fresh3 $ \a b body -> do
        e <=> lam body
        ty <=> tarr a b
        call $ infer (econs a env) body b
        pure ()
    , -- App: Γ ⊢ e₁ : A → B   Γ ⊢ e₂ : A  =>  Γ ⊢ e₁ e₂ : B
      fresh3 $ \e1 e2 a -> do
        e <=> app e1 e2
        call $ infer env e1 (tarr a ty)
        call $ infer env e2 a
        pure ()
    , -- Let: Γ ⊢ e₁ : A   Γ, x:A ⊢ e₂ : B  =>  Γ ⊢ let x = e₁ in e₂ : B
      -- (No generalization for simplicity)
      fresh3 $ \e1 e2 a -> do
        e <=> letIn e1 e2
        call $ infer env e1 a
        call $ infer (econs a env) e2 ty
        pure ()
    ]

-- Run inference in mode (I,I,O)
inferIO :: Env -> Tm -> Stream Ty
inferIO env0 e0 = runSubstRedex $ fresh $ \ty -> do
  _ <- embed $ infer (Ground $ project env0) (Ground $ project e0) ty
  eval ty

-- Run inference in mode (I,O,I): given env and type, synthesize term
inferOI :: Env -> Ty -> Stream Tm
inferOI env0 ty0 = runSubstRedex $ fresh $ \e -> do
  _ <- embed $ infer (Ground $ project env0) e (Ground $ project ty0)
  eval e

main :: IO ()
main = do
  putStrLn "=== Hindley-Milner Type Inference ==="
  putStrLn ""

  -- Example 1: Unit constant
  putStrLn "Infer: ()"
  print $ takeS 1 (inferIO ENil Unit)
  putStrLn ""

  -- Example 2: Application (λx.x) ()
  let app_id = App (Lam (Var Z)) Unit
  putStrLn "Infer: (λx. x) ()"
  print $ takeS 1 (inferIO ENil app_id)
  putStrLn ""

  -- Example 3: Nested application (λx.λy.y) () ()
  let ex3 = App (App (Lam (Lam (Var Z))) Unit) Unit
  putStrLn "Infer: (λx. λy. y) () ()"
  print $ takeS 1 (inferIO ENil ex3)
  putStrLn ""

  -- Example 4: let x = () in x
  let let_id = Let Unit (Var Z)
  putStrLn "Infer: let x = () in x"
  print $ takeS 1 (inferIO ENil let_id)
  putStrLn ""

  -- Example 5: (λf. f ()) (λx. x)
  let ex5 = App (Lam (App (Var Z) Unit)) (Lam (Var Z))
  putStrLn "Infer: (λf. f ()) (λx. x)"
  print $ takeS 1 (inferIO ENil ex5)
  putStrLn ""

  -- Example 6: Checking a term against a type
  -- Check if () has type Unit
  putStrLn "Check: () has type Unit"
  let check_unit = runSubstRedex $ do
        _ <- embed $ infer enil (Ground $ project Unit) tunit
        pure ()
  print $ takeS 1 check_unit
  putStrLn ""

  -- Example 7: Term synthesis - find a term of type Unit
  putStrLn "Synthesize term of type Unit"
  print $ takeS 3 (inferOI ENil TUnit)
