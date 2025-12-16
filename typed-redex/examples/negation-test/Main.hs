{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Main (main) where

import Control.Applicative (empty)
import TypedRedex.Core.Redex
import TypedRedex.Core.Internal.Logic (Logic (Ground), LogicType (..))
import TypedRedex.Interpreters.SubstRedex (runSubstRedex, takeS, Stream)
import TypedRedex.Utils.Redex
import TypedRedex.Utils.Type (quote0, quote1)

-- | Natural numbers
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

zro, one, two :: Logic Nat var
zro = Ground ZR
one = Ground (SR zro)
two = Ground (SR one)

-- | Test 1: neg succeeds when goal fails
-- neg(Z = S(Z)) should succeed
test1 :: Stream ()
test1 = runSubstRedex $ neg (zro <=> one)

-- | Test 2: neg fails when goal succeeds
-- neg(Z = Z) should fail
test2 :: Stream ()
test2 = runSubstRedex $ neg (zro <=> zro)

-- | Test 3: neg with fresh variable - fails because goal has solution
test3 :: Stream ()
test3 = runSubstRedex $ fresh $ \x -> neg (x <=> zro)

-- | Test 4: neg with constrained variable
-- x = S(Z), neg(x = Z) should succeed
test4 :: Stream Nat
test4 = runSubstRedex $ fresh $ \x -> do
  x <=> one
  neg (x <=> zro)
  eval x

-- | Test 5: Using neg to filter
-- Find x in {Z, S(Z)} such that x is not Z
test5 :: Stream Nat
test5 = runSubstRedex $ fresh $ \x -> do
  conde [x <=> zro, x <=> one]
  neg (x <=> zro)
  eval x

showResults :: Show a => String -> Stream a -> IO ()
showResults name stream = putStrLn $ name ++ ": " ++ show (takeS 10 stream)

main :: IO ()
main = do
  putStrLn "=== Negation Tests ==="
  putStrLn ""
  putStrLn "Test 1: neg(Z = S(Z)) - should succeed"
  showResults "  Result" test1
  putStrLn ""
  putStrLn "Test 2: neg(Z = Z) - should fail"
  showResults "  Result" test2
  putStrLn ""
  putStrLn "Test 3: neg(x = Z) with fresh x - should fail"
  showResults "  Result" test3
  putStrLn ""
  putStrLn "Test 4: x = S(Z), neg(x = Z) - should succeed with S(Z)"
  showResults "  Result" test4
  putStrLn ""
  putStrLn "Test 5: x in {Z, S(Z)}, neg(x = Z) - should give S(Z)"
  showResults "  Result" test5
