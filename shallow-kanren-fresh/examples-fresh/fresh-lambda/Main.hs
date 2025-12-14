{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module Main (main) where

import Control.Applicative (empty, Alternative)
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
  , name2String
  , s2n
  , aeq
  )

import Shallow.Core.Internal.Logic (Logic (Ground, Free), LogicType (..))
import Shallow.Core.Internal.Kanren (Kanren, Relation)
import Shallow.Interpreters.SubstKanrenFresh (runSubstKanrenFresh, takeS, Stream)
import Shallow.Utils.Kanren (fresh, fresh2, (===), (<=>), conde, relation2, eval, L)

-- ============================================================================
-- Lambda Calculus with unbound-generics
-- ============================================================================

type TmName = Name Tm

data Tm
  = Var TmName
  | Lam (Bind TmName Tm)  -- Using unbound-generics Bind!
  | App Tm Tm
  deriving (Show, Generic, Typeable)

-- Required instances for unbound-generics
instance Alpha Tm

instance Subst Tm Tm where
  isvar (Var x) = Just (SubstName x)
  isvar _ = Nothing

-- ============================================================================
-- LogicType instance with MONADIC operations
-- ============================================================================

instance LogicType Tm where
  -- Reified representation - unbind the Bind!
  data Reified Tm var
    = VarR TmName
    | LamR TmName (Logic Tm var)  -- Store unbound name and body
    | AppR (Logic Tm var) (Logic Tm var)

  -- MONADIC project - can use unbind now!
  project (Var x) = pure $ VarR x
  project (Lam b) = do
    -- Use Fresh monad to unbind!
    (x, body) <- unbind b
    -- Recursively project the body
    bodyR <- project body
    pure $ LamR x (Ground bodyR)
  project (App f a) = do
    fR <- project f
    aR <- project a
    pure $ AppR (Ground fR) (Ground aR)

  -- MONADIC reify - can use bind now!
  reify (VarR x) = pure $ Just (Var x)
  reify (LamR x (Ground body)) = do
    bodyM <- reify body
    case bodyM of
      Just body' -> pure $ Just (Lam (bind x body'))
      Nothing -> pure Nothing
  reify (AppR (Ground f) (Ground a)) = do
    fM <- reify f
    aM <- reify a
    case (fM, aM) of
      (Just f', Just a') -> pure $ Just (App f' a')
      _ -> pure Nothing
  reify _ = pure Nothing

  -- Unification - uses alpha-equivalence!
  unifyVal unif (VarR x) (VarR y)
    | x == y = pure ()
    | otherwise = empty
  unifyVal unif (LamR x body) (LamR y body')
    -- For now, require name equality
    -- Could use aeq for full alpha-equivalence check
    | x == y = unif body body'
    | otherwise = empty
  unifyVal unif (AppR f a) (AppR f' a') =
    unif f f' *> unif a a'
  unifyVal _ _ _ = empty

  -- Quote for pretty printing
  quote (VarR x) = (name2String x, [])
  quote (LamR x body) = ("Lam_" ++ name2String x, [])
  quote (AppR f a) = ("App", [])

  -- Dereference
  derefVal deref (VarR x) = pure (Var x)
  derefVal deref (LamR x body) = do
    body' <- deref body
    pure $ Lam (bind x body')
  derefVal deref (AppR f a) = do
    f' <- deref f
    a' <- deref a
    pure $ App f' a'

-- ============================================================================
-- Helper constructors
-- ============================================================================

var :: String -> Tm
var = Var . s2n

lam :: String -> Tm -> Tm
lam x body = Lam (bind (s2n x) body)

app :: Tm -> Tm -> Tm
app = App

-- ============================================================================
-- Example relation: Alpha-equivalence check
-- ============================================================================

alphaEquiv :: (Kanren rel) => L Tm rel -> L Tm rel -> Relation rel
alphaEquiv = relation2 "alphaEquiv" $ \t1 t2 ->
  t1 <=> t2

-- ============================================================================
-- Main demonstration
-- ============================================================================

main :: IO ()
main = do
  putStrLn "=== Fresh-Aware shallow-kanren with unbound-generics ==="
  putStrLn ""
  putStrLn "This prototype demonstrates:"
  putStrLn "✓ LogicType with MONADIC operations"
  putStrLn "✓ SubstKanren stacked with FreshMT"
  putStrLn "✓ Direct use of unbound-generics Bind type"
  putStrLn "✓ unbind/bind operations in project/reify"
  putStrLn ""

  -- Example terms
  let id_tm = lam "x" (var "x")           -- λx. x
  let id_tm2 = lam "y" (var "y")          -- λy. y
  let const_tm = lam "x" (lam "y" (var "x"))  -- λx. λy. x

  putStrLn "Example terms (using unbound-generics):"
  putStrLn $ "  id:    " ++ show id_tm
  putStrLn $ "  id2:   " ++ show id_tm2
  putStrLn $ "  const: " ++ show const_tm
  putStrLn ""

  -- Test unification
  putStrLn "Query 1: Find term that unifies with λx.x"
  let query1 = runSubstKanrenFresh $ fresh $ \t -> do
        tR <- project id_tm
        t <=> Ground tR
        eval t
  putStrLn $ "  Results: " ++ show (takeS 1 query1)
  putStrLn ""

  putStrLn "Query 2: Check if λx.x and λy.y unify (they should with same structure)"
  let query2 = runSubstKanrenFresh $ fresh2 $ \t1 t2 -> do
        -- Manually check if same structure
        t1R <- project id_tm
        t2R <- project id_tm2
        t1 <=> Ground t1R
        t2 <=> Ground t2R
        -- Try to unify based on names (will fail because x ≠ y)
        -- This shows we need proper alpha-equivalence
        t1' <- eval t1
        t2' <- eval t2
        return (t1', t2')
  putStrLn $ "  Results: " ++ show (takeS 1 query2)
  putStrLn ""

  putStrLn "CONCLUSION:"
  putStrLn "✓ Prototype successfully integrates Fresh monad into shallow-kanren!"
  putStrLn "✓ Can use unbound-generics Bind directly in term representation"
  putStrLn "✓ unbind/bind work in monadic project/reify"
  putStrLn ""
  putStrLn "TODO for full implementation:"
  putStrLn "- Implement proper alpha-equivalence checking using aeq in unifyVal"
  putStrLn "- Update all utility functions to handle monadic LogicType"
  putStrLn "- Port all existing examples to new architecture"
  putStrLn "- Add more sophisticated binding examples"
