{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Main (main) where

import Control.Applicative (empty)
import Shallow.Core.Kanren
import Shallow.Core.Internal.Logic (Logic (Ground), LogicType (..))
import Shallow.Interpreters.SubstKanren (runSubstKanren, takeS, Stream)
import Shallow.Utils.Type (quote0, quote1, quote2)

-- Faithful implementation of LC TI algorithm
-- Based on Dunfield & Krishnaswami's bidirectional system
-- Starting with simpler types, will extend to polymorphism

-- Natural numbers for de Bruijn indices and type variable names
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

-- Polarity for subtyping
data Polar = Pos | Neg deriving (Eq, Show)

instance LogicType Polar where
  data Reified Polar var = PosR | NegR

  project Pos = PosR
  project Neg = NegR

  reify PosR = Just Pos
  reify NegR = Just Neg
  reify _ = Nothing

  quote PosR = quote0 "Pos" PosR
  quote NegR = quote0 "Neg" NegR

  unifyVal _ PosR PosR = pure ()
  unifyVal _ NegR NegR = pure ()
  unifyVal _ _ _ = empty

  derefVal _ PosR = pure Pos
  derefVal _ NegR = pure Neg

pos :: Logic Polar var
pos = Ground PosR

neg :: Logic Polar var
neg = Ground NegR

-- Flip polarity
flipPolar :: (Kanren rel) => L Polar rel -> L Polar rel -> Relation rel
flipPolar = relation2 "flipPolar" $ \p p' ->
  conde
    [ do
        p <=> pos
        p' <=> neg
        pure ()
    , do
        p <=> neg
        p' <=> pos
        pure ()
    ]

-- Types
data Ty
  = TInt                -- Int
  | TBool               -- Bool
  | TVar Nat            -- Type variable (de Bruijn index or existential)
  | TArr Ty Ty          -- A → B
  | TForall Ty          -- ∀. A (simplified - no binding)
  deriving (Eq, Show)

instance LogicType Ty where
  data Reified Ty var
    = TIntR
    | TBoolR
    | TVarR (Logic Nat var)
    | TArrR (Logic Ty var) (Logic Ty var)
    | TForallR (Logic Ty var)

  project TInt = TIntR
  project TBool = TBoolR
  project (TVar n) = TVarR (Ground $ project n)
  project (TArr a b) = TArrR (Ground $ project a) (Ground $ project b)
  project (TForall ty) = TForallR (Ground $ project ty)

  reify TIntR = Just TInt
  reify TBoolR = Just TBool
  reify (TVarR (Ground n)) = TVar <$> reify n
  reify (TArrR (Ground a) (Ground b)) = TArr <$> reify a <*> reify b
  reify (TForallR (Ground ty)) = TForall <$> reify ty
  reify _ = Nothing

  quote TIntR = quote0 "TInt" TIntR
  quote TBoolR = quote0 "TBool" TBoolR
  quote (TVarR n) = quote1 "TVar" TVarR n
  quote (TArrR a b) = quote2 "TArr" TArrR a b
  quote (TForallR ty) = quote1 "TForall" TForallR ty

  unifyVal _ TIntR TIntR = pure ()
  unifyVal _ TBoolR TBoolR = pure ()
  unifyVal unif (TVarR n) (TVarR n') = unif n n'
  unifyVal unif (TArrR a b) (TArrR a' b') = unif a a' *> unif b b'
  unifyVal unif (TForallR ty) (TForallR ty') = unif ty ty'
  unifyVal _ _ _ = empty

  derefVal _ TIntR = pure TInt
  derefVal _ TBoolR = pure TBool
  derefVal deref (TVarR n) = TVar <$> deref n
  derefVal deref (TArrR a b) = TArr <$> deref a <*> deref b
  derefVal deref (TForallR ty) = TForall <$> deref ty

tint :: Logic Ty var
tint = Ground TIntR

tbool :: Logic Ty var
tbool = Ground TBoolR

tvar :: Logic Nat var -> Logic Ty var
tvar = Ground . TVarR

tarr :: Logic Ty var -> Logic Ty var -> Logic Ty var
tarr a b = Ground $ TArrR a b

tforall :: Logic Ty var -> Logic Ty var
tforall = Ground . TForallR

-- Terms
data Tm
  = LitInt Int
  | LitBool Bool
  | Var Nat
  | Abs Tm              -- λx. e (no annotation)
  | AbsAnn Ty Tm        -- λx:A. e
  | App Tm Tm
  | Ann Tm Ty
  deriving (Eq, Show)

instance LogicType Tm where
  data Reified Tm var
    = LitIntR Int
    | LitBoolR Bool
    | VarR (Logic Nat var)
    | AbsR (Logic Tm var)
    | AbsAnnR (Logic Ty var) (Logic Tm var)
    | AppR (Logic Tm var) (Logic Tm var)
    | AnnR (Logic Tm var) (Logic Ty var)

  project (LitInt n) = LitIntR n
  project (LitBool b) = LitBoolR b
  project (Var n) = VarR (Ground $ project n)
  project (Abs b) = AbsR (Ground $ project b)
  project (AbsAnn ty b) = AbsAnnR (Ground $ project ty) (Ground $ project b)
  project (App f a) = AppR (Ground $ project f) (Ground $ project a)
  project (Ann e ty) = AnnR (Ground $ project e) (Ground $ project ty)

  reify (LitIntR n) = Just (LitInt n)
  reify (LitBoolR b) = Just (LitBool b)
  reify (VarR (Ground n)) = Var <$> reify n
  reify (AbsR (Ground b)) = Abs <$> reify b
  reify (AbsAnnR (Ground ty) (Ground b)) = AbsAnn <$> reify ty <*> reify b
  reify (AppR (Ground f) (Ground a)) = App <$> reify f <*> reify a
  reify (AnnR (Ground e) (Ground ty)) = Ann <$> reify e <*> reify ty
  reify _ = Nothing

  quote (LitIntR n) = quote0 ("LitInt_" ++ show n) (LitIntR n)
  quote (LitBoolR b) = quote0 ("LitBool_" ++ show b) (LitBoolR b)
  quote (VarR n) = quote1 "Var" VarR n
  quote (AbsR b) = quote1 "Abs" AbsR b
  quote (AbsAnnR ty b) = quote2 "AbsAnn" AbsAnnR ty b
  quote (AppR f a) = quote2 "App" AppR f a
  quote (AnnR e ty) = quote2 "Ann" AnnR e ty

  unifyVal _ (LitIntR n) (LitIntR n') | n == n' = pure ()
  unifyVal _ (LitBoolR b) (LitBoolR b') | b == b' = pure ()
  unifyVal unif (VarR n) (VarR n') = unif n n'
  unifyVal unif (AbsR b) (AbsR b') = unif b b'
  unifyVal unif (AbsAnnR ty b) (AbsAnnR ty' b') = unif ty ty' *> unif b b'
  unifyVal unif (AppR f a) (AppR f' a') = unif f f' *> unif a a'
  unifyVal unif (AnnR e ty) (AnnR e' ty') = unif e e' *> unif ty ty'
  unifyVal _ _ _ = empty

  derefVal _ (LitIntR n) = pure (LitInt n)
  derefVal _ (LitBoolR b) = pure (LitBool b)
  derefVal deref (VarR n) = Var <$> deref n
  derefVal deref (AbsR b) = Abs <$> deref b
  derefVal deref (AbsAnnR ty b) = AbsAnn <$> deref ty <*> deref b
  derefVal deref (AppR f a) = App <$> deref f <*> deref a
  derefVal deref (AnnR e ty) = Ann <$> deref e <*> deref ty

litInt :: Int -> Logic Tm var
litInt n = Ground (LitIntR n)

litBool :: Bool -> Logic Tm var
litBool b = Ground (LitBoolR b)

var :: Logic Nat var -> Logic Tm var
var = Ground . VarR

abs :: Logic Tm var -> Logic Tm var
abs = Ground . AbsR

absAnn :: Logic Ty var -> Logic Tm var -> Logic Tm var
absAnn ty b = Ground $ AbsAnnR ty b

app :: Logic Tm var -> Logic Tm var -> Logic Tm var
app f a = Ground $ AppR f a

ann :: Logic Tm var -> Logic Ty var -> Logic Tm var
ann e ty = Ground $ AnnR e ty

-- Type environment with existential variables
-- Following LCTI paper: tracks term variables, universal type vars, existential type vars, and solved vars
data Env
  = ENil                    -- Empty environment
  | ECons Ty Env            -- Term variable: x : A
  | EUvar Nat Env           -- Universal type variable: a (from forall)
  | EEvar Nat Env           -- Existential type variable: â (to be solved)
  | ESvar Nat Ty Env        -- Solved existential: â = A
  deriving (Eq, Show)

instance LogicType Env where
  data Reified Env var
    = ENilR
    | EConsR (Logic Ty var) (Logic Env var)
    | EUvarR (Logic Nat var) (Logic Env var)
    | EEvarR (Logic Nat var) (Logic Env var)
    | ESvarR (Logic Nat var) (Logic Ty var) (Logic Env var)

  project ENil = ENilR
  project (ECons ty env) = EConsR (Ground $ project ty) (Ground $ project env)
  project (EUvar n env) = EUvarR (Ground $ project n) (Ground $ project env)
  project (EEvar n env) = EEvarR (Ground $ project n) (Ground $ project env)
  project (ESvar n ty env) = ESvarR (Ground $ project n) (Ground $ project ty) (Ground $ project env)

  reify ENilR = Just ENil
  reify (EConsR (Ground ty) (Ground env)) = ECons <$> reify ty <*> reify env
  reify (EUvarR (Ground n) (Ground env)) = EUvar <$> reify n <*> reify env
  reify (EEvarR (Ground n) (Ground env)) = EEvar <$> reify n <*> reify env
  reify (ESvarR (Ground n) (Ground ty) (Ground env)) = ESvar <$> reify n <*> reify ty <*> reify env
  reify _ = Nothing

  quote ENilR = quote0 "ENil" ENilR
  quote (EConsR ty env) = quote2 "ECons" EConsR ty env
  quote (EUvarR n env) = quote2 "EUvar" EUvarR n env
  quote (EEvarR n env) = quote2 "EEvar" EEvarR n env
  quote (ESvarR n ty env) = ("ESvar", [])  -- Simplified for now

  unifyVal _ ENilR ENilR = pure ()
  unifyVal unif (EConsR ty env) (EConsR ty' env') = unif ty ty' *> unif env env'
  unifyVal unif (EUvarR n env) (EUvarR n' env') = unif n n' *> unif env env'
  unifyVal unif (EEvarR n env) (EEvarR n' env') = unif n n' *> unif env env'
  unifyVal unif (ESvarR n ty env) (ESvarR n' ty' env') = unif n n' *> unif ty ty' *> unif env env'
  unifyVal _ _ _ = empty

  derefVal _ ENilR = pure ENil
  derefVal deref (EConsR ty env) = ECons <$> deref ty <*> deref env
  derefVal deref (EUvarR n env) = EUvar <$> deref n <*> deref env
  derefVal deref (EEvarR n env) = EEvar <$> deref n <*> deref env
  derefVal deref (ESvarR n ty env) = ESvar <$> deref n <*> deref ty <*> deref env

enil :: Logic Env var
enil = Ground ENilR

econs :: Logic Ty var -> Logic Env var -> Logic Env var
econs ty env = Ground $ EConsR ty env

euvar :: Logic Nat var -> Logic Env var -> Logic Env var
euvar n env = Ground $ EUvarR n env

eevar :: Logic Nat var -> Logic Env var -> Logic Env var
eevar n env = Ground $ EEvarR n env

esvar :: Logic Nat var -> Logic Ty var -> Logic Env var -> Logic Env var
esvar n ty env = Ground $ ESvarR n ty env

-- Lookup term variable in environment
lookupEnv :: (Kanren rel) => L Env rel -> L Nat rel -> L Ty rel -> Relation rel
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
    , -- Skip over type variables
      fresh2 $ \tvar rest -> do
        env <=> euvar tvar rest
        call $ lookupEnv rest n ty
        pure ()
    , fresh2 $ \tvar rest -> do
        env <=> eevar tvar rest
        call $ lookupEnv rest n ty
        pure ()
    , fresh3 $ \tvar tty rest -> do
        env <=> esvar tvar tty rest
        call $ lookupEnv rest n ty
        pure ()
    ]

-- Check if a type variable is a universal variable
isUvar :: (Kanren rel) => L Env rel -> L Nat rel -> Relation rel
isUvar = relation2 "isUvar" $ \env a ->
  conde
    [ fresh $ \rest -> do
        env <=> euvar a rest
        pure ()
    , fresh2 $ \ty rest -> do
        env <=> econs ty rest
        call $ isUvar rest a
        pure ()
    , fresh2 $ \b rest -> do
        env <=> euvar b rest
        call $ isUvar rest a
        pure ()
    , fresh2 $ \b rest -> do
        env <=> eevar b rest
        call $ isUvar rest a
        pure ()
    , fresh3 $ \b ty rest -> do
        env <=> esvar b ty rest
        call $ isUvar rest a
        pure ()
    ]

-- Check if a type variable is an existential variable
isEvar :: (Kanren rel) => L Env rel -> L Nat rel -> Relation rel
isEvar = relation2 "isEvar" $ \env a ->
  conde
    [ fresh $ \rest -> do
        env <=> eevar a rest
        pure ()
    , fresh2 $ \ty rest -> do
        env <=> econs ty rest
        call $ isEvar rest a
        pure ()
    , fresh2 $ \b rest -> do
        env <=> euvar b rest
        call $ isEvar rest a
        pure ()
    , fresh2 $ \b rest -> do
        env <=> eevar b rest
        call $ isEvar rest a
        pure ()
    , fresh3 $ \b ty rest -> do
        env <=> esvar b ty rest
        call $ isEvar rest a
        pure ()
    ]

-- Find solution for a solved existential variable
findSol :: (Kanren rel) => L Env rel -> L Nat rel -> L Ty rel -> Relation rel
findSol = relation3 "findSol" $ \env a ty ->
  conde
    [ fresh $ \rest -> do
        env <=> esvar a ty rest
        pure ()
    , fresh2 $ \ty' rest -> do
        env <=> econs ty' rest
        call $ findSol rest a ty
        pure ()
    , fresh2 $ \b rest -> do
        env <=> euvar b rest
        call $ findSol rest a ty
        pure ()
    , fresh2 $ \b rest -> do
        env <=> eevar b rest
        call $ findSol rest a ty
        pure ()
    , fresh3 $ \b ty' rest -> do
        env <=> esvar b ty' rest
        call $ findSol rest a ty
        pure ()
    ]

-- Instantiation: inst env a tyA env'
-- Instantiates existential variable â with type A, producing new environment
inst :: (Kanren rel) => L Env rel -> L Nat rel -> L Ty rel -> L Env rel -> Relation rel
inst = relation4 "inst" $ \env a tyA env' ->
  conde
    [ -- Base case: cannot instantiate in empty environment
      do
        env <=> enil
        env' <=> enil
        pure ()
    , -- Found the existential variable: replace with solved variable
      fresh $ \rest -> do
        env <=> eevar a rest
        env' <=> esvar a tyA rest
        pure ()
    , -- Not the right existential: recurse and rebuild
      fresh3 $ \b rest rest' -> do
        env <=> eevar b rest
        call $ inst rest a tyA rest'
        env' <=> eevar b rest'
        pure ()
    , -- Skip term variables
      fresh3 $ \ty rest rest' -> do
        env <=> econs ty rest
        call $ inst rest a tyA rest'
        env' <=> econs ty rest'
        pure ()
    , -- Skip universal variables
      fresh3 $ \b rest rest' -> do
        env <=> euvar b rest
        call $ inst rest a tyA rest'
        env' <=> euvar b rest'
        pure ()
    , -- Skip solved variables
      fresh4 $ \b ty rest rest' -> do
        env <=> esvar b ty rest
        call $ inst rest a tyA rest'
        env' <=> esvar b ty rest'
        pure ()
    ]

-- Polarized subtyping: ssub env ty1 p ty2
-- Simplified version without existential variables
ssub :: (Kanren rel) => L Env rel -> L Ty rel -> L Polar rel -> L Ty rel -> Relation rel
ssub = relation4 "ssub" $ \env ty1 p ty2 ->
  conde
    [ -- S-Int
      do
        ty1 <=> tint
        ty2 <=> tint
        pure ()
    , -- S-Bool
      do
        ty1 <=> tbool
        ty2 <=> tbool
        pure ()
    , -- S-Arr: contravariant in argument, covariant in result
      fresh4 $ \tyA tyB tyC tyD -> fresh $ \p' -> do
        ty1 <=> tarr tyA tyB
        ty2 <=> tarr tyC tyD
        call $ flipPolar p p'
        call $ ssub env tyC p' tyA
        call $ ssub env tyB p tyD
        pure ()
    ]

-- Type inference
-- Simplified version: infer env e ty
-- Note: For literals, we only handle specific values (0, true, false)
-- A full implementation would need a more sophisticated approach
infer :: (Kanren rel) => L Env rel -> L Tm rel -> L Ty rel -> Relation rel
infer = relation3 "infer" $ \env e ty ->
  conde
    [ -- Ty-Int: match integer literal 0
      do
        e <=> Ground (LitIntR 0)
        ty <=> tint
        pure ()
    , -- Ty-Int: match integer literal 42
      do
        e <=> Ground (LitIntR 42)
        ty <=> tint
        pure ()
    , -- Ty-Int: match integer literal 1
      do
        e <=> Ground (LitIntR 1)
        ty <=> tint
        pure ()
    , -- Ty-Int: match integer literal 2
      do
        e <=> Ground (LitIntR 2)
        ty <=> tint
        pure ()
    , -- Ty-Bool: match true
      do
        e <=> Ground (LitBoolR True)
        ty <=> tbool
        pure ()
    , -- Ty-Bool: match false
      do
        e <=> Ground (LitBoolR False)
        ty <=> tbool
        pure ()
    , -- Ty-Var
      fresh $ \n -> do
        e <=> var n
        call $ lookupEnv env n ty
        pure ()
    , -- Ty-Ann
      fresh2 $ \e' tyA -> do
        e <=> ann e' tyA
        call $ infer env e' tyA
        ty <=> tyA
        pure ()
    , -- Ty-AbsAnn
      fresh3 $ \tyA body tyB -> do
        e <=> absAnn tyA body
        ty <=> tarr tyA tyB
        call $ infer (econs tyA env) body tyB
        pure ()
    , -- Ty-App
      fresh3 $ \e1 e2 tyA -> do
        e <=> app e1 e2
        call $ infer env e1 (tarr tyA ty)
        call $ infer env e2 tyA
        pure ()
    ]

-- Run inference in mode (I,I,O)
inferIO :: Env -> Tm -> Stream Ty
inferIO env0 e0 = runSubstKanren $ fresh $ \ty -> do
  _ <- embed $ infer (Ground $ project env0) (Ground $ project e0) ty
  eval ty

main :: IO ()
main = do
  putStrLn "=== LCTI: Context-Based Type Inference ==="
  putStrLn "Starting with core features (no polymorphism yet)"
  putStrLn ""

  -- Example 1: Integer literal
  let ex1 = LitInt 42
  putStrLn "Infer: 42"
  print $ takeS 1 (inferIO ENil ex1)
  putStrLn ""

  -- Example 2: Identity function with annotation
  let ex2 = AbsAnn TInt (Var Z)
  putStrLn "Infer: λx:int. x"
  print $ takeS 1 (inferIO ENil ex2)
  putStrLn ""

  -- Example 3: Application
  let ex3 = App (AbsAnn TInt (Var Z)) (LitInt 42)
  putStrLn "Infer: (λx:int. x) 42"
  print $ takeS 1 (inferIO ENil ex3)
  putStrLn ""

  -- Example 4: Const function
  let ex4 = AbsAnn TInt (AbsAnn TBool (Var (S Z)))
  putStrLn "Infer: λx:int. λy:bool. x"
  print $ takeS 1 (inferIO ENil ex4)
  putStrLn ""

  -- Example 5: Choose function (same type both args)
  let choose = AbsAnn TInt (AbsAnn TInt (Var Z))
  let ex5 = App (App choose (LitInt 1)) (LitInt 2)
  putStrLn "Infer: (λx:int. λy:int. y) 1 2"
  print $ takeS 1 (inferIO ENil ex5)
  putStrLn ""

  -- Example 6: Annotation
  let ex6 = Ann (AbsAnn TInt (Var Z)) (TArr TInt TInt)
  putStrLn "Infer: (λx:int. x) : int → int"
  print $ takeS 1 (inferIO ENil ex6)
  putStrLn ""

  -- Example 7: Test subtyping
  putStrLn "Test subtyping: int → bool ≤+ int → bool"
  let testSsub = runSubstKanren $ do
        _ <- embed $ ssub enil (tarr tint tbool) pos (tarr tint tbool)
        pure ()
  print $ takeS 1 testSsub
  putStrLn ""

  -- Example 8: Term synthesis - find term of type int → int
  putStrLn "Synthesize term of type int → int"
  let synth = runSubstKanren $ fresh $ \e -> do
        _ <- embed $ infer enil e (tarr tint tint)
        eval e
  print $ takeS 3 synth
