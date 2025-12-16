{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Main (main) where

import Control.Applicative (empty)
import GHC.Generics (Generic)
import Data.Typeable (Typeable)

import Unbound.Generics.LocallyNameless
    ( Name
    , Bind
    , bind
    , unbind
    , Alpha
    , Subst(..)
    , SubstName(..)
    , Fresh
    , runFreshM
    , name2String
    , s2n
    )

import TypedRedex.Core.Redex
import TypedRedex.Core.Internal.Logic (Logic (Ground), LogicType (..))
import TypedRedex.Interpreters.SubstRedex (runSubstRedex, takeS, Stream)
import TypedRedex.Utils.Type (quote0, quote1, quote2)

-- Test: Can we use unbound-generics with shallow-kanren?
--
-- The challenge: unbound-generics uses:
--   - Bind for binders (requires Fresh monad)
--   - Alpha equivalence for structural equality
--   - Name type for variables
--
-- While shallow-kanren uses:
--   - Logic variables and unification
--   - Structural equality on Reified types
--   - No monadic context for fresh names

type TmName = Name Tm

-- Simple lambda calculus with named variables
data Tm
  = Var TmName
  | Lam (Bind TmName Tm)  -- λx. e with binding
  | App Tm Tm
  deriving (Generic, Typeable, Show)

-- Required instances for unbound-generics
instance Alpha Tm

instance Subst Tm Tm where
  isvar (Var x) = Just (SubstName x)
  isvar _ = Nothing

-- The key question: Can we define LogicType for types with Bind?
-- The problem: Bind requires Fresh monad for unbinding
--             LogicType requires pure functions
instance LogicType Tm where
  data Reified Tm var
    = VarR TmName  -- Store the name directly (no logic variable)
    | LamR (Bind TmName (Logic Tm var))  -- Bind with logic term inside
    | AppR (Logic Tm var) (Logic Tm var)

  -- Project from Haskell term to reified form
  -- Problem: We need to handle Bind, which requires Fresh monad
  project (Var x) = VarR x
  project (Lam b) =
    -- PROBLEM 1: Can't unbind without Fresh monad
    -- unbind :: Fresh m => Bind n t -> m (n, t)
    -- But project :: Tm -> Reified Tm var must be pure!
    --
    -- Even if we store the Bind directly:
    LamR b  -- Would need: Bind TmName (Logic Tm var)
            -- But we have: Bind TmName Tm
            -- Can't convert without Fresh monad to unbind and rebind
  project (App f a) = AppR (Ground $ project f) (Ground $ project a)

  -- Reify back to Haskell term
  -- Problem: Again need Fresh monad to work with Bind
  reify (VarR x) = Just (Var x)
  reify (LamR b) = do
    -- Can't unbind here either!
    -- fmap Lam (unbind b)  -- unbind :: Fresh m => Bind n t -> m (n, t)
    Nothing  -- Have to fail here
  reify (AppR (Ground f) (Ground a)) = App <$> reify f <*> reify a
  reify _ = Nothing

  -- Quote for pretty printing
  quote (VarR x) = quote0 (name2String x) (VarR x)
  quote (LamR _) = ("Lam", [])  -- Can't properly quote without Fresh monad
  quote (AppR f a) = quote2 "App" AppR f a

  -- Unification: The critical problem!
  -- Alpha equivalence requires Fresh monad: aeq :: Fresh m => t -> t -> m Bool
  -- But unifyVal must be pure!
  unifyVal _ (VarR x) (VarR y) | x == y = pure ()  -- Name equality, not alpha-eq
  unifyVal _ (LamR _) (LamR _) = empty  -- Can't implement without Fresh!
  unifyVal unif (AppR f a) (AppR f' a') = unif f f' *> unif a a'
  unifyVal _ _ _ = empty

  -- Dereference
  derefVal _ (VarR x) = pure (Var x)
  derefVal _ (LamR _) = empty  -- Can't implement
  derefVal deref (AppR f a) = App <$> deref f <*> deref a

main :: IO ()
main = do
  putStrLn "=== Test: unbound-generics with shallow-kanren ==="
  putStrLn ""
  putStrLn "CONCLUSION: Integration is fundamentally incompatible!"
  putStrLn ""
  putStrLn "Reasons:"
  putStrLn "1. unbound-generics requires Fresh monad for unbinding"
  putStrLn "   - unbind :: Fresh m => Bind n t -> m (n, t)"
  putStrLn "   - But LogicType methods must be pure (no monad)"
  putStrLn ""
  putStrLn "2. Alpha equivalence requires Fresh monad"
  putStrLn "   - aeq :: Fresh m => t -> t -> m Bool"
  putStrLn "   - But unifyVal :: Reified t var -> Reified t var -> rel ()"
  putStrLn "   - Cannot lift Fresh into the rel monad"
  putStrLn ""
  putStrLn "3. Bind is not a Functor/Traversable in the way we need"
  putStrLn "   - Can't map (Ground . project) over terms inside Bind"
  putStrLn "   - Would need Fresh monad to unbind first"
  putStrLn ""
  putStrLn "ALTERNATIVES:"
  putStrLn "1. Use de Bruijn indices (current approach)"
  putStrLn "   ✓ No monadic overhead"
  putStrLn "   ✓ Alpha equivalence is structural equality"
  putStrLn "   ✓ Clean integration with LogicType"
  putStrLn ""
  putStrLn "2. Use named representation WITHOUT unbound-generics"
  putStrLn "   ✓ Store names as regular Strings/Ints"
  putStrLn "   ✓ Handle freshness manually in relations"
  putStrLn "   - Lose automatic alpha-equivalence"
  putStrLn "   - More manual work for capture-avoiding substitution"
  putStrLn ""
  putStrLn "RECOMMENDATION: Continue with de Bruijn indices"
  putStrLn "They are idiomatic for relational programming and avoid all these issues."
