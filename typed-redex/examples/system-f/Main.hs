{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ImplicitParams #-}

module Main (main) where

import Control.Applicative (empty)
import TypedRedex.Core.Redex
import TypedRedex.Core.Internal.Logic (Logic (Ground), LogicType (..))
import TypedRedex.Interpreters.SubstRedex (runSubstRedex, takeS, Stream)
import TypedRedex.Utils.Type (quote0, quote1, quote2)

import Syntax

-- Aliases for binary relations (most common case)
concl :: (?conclArgs :: (L a rel, L b rel), Redex rel, LogicType a, LogicType b)
      => Applied2 rel a b -> rel ()
concl = concl2

-- Alias for ternary conclusion
concl3' :: (?conclArgs :: (L a rel, L b rel, L c rel), Redex rel, LogicType a, LogicType b, LogicType c)
        => Applied3 rel a b c -> rel ()
concl3' = concl3

-- Nat equality check
natEq :: (Redex rel) => L Nat rel -> L Nat rel -> Applied2 rel Nat Nat
natEq = define2 "natEq"
  [ concl $ natEq zro zro
  , fresh2 $ \n' m' -> do
      concl $ natEq (suc n') (suc m')
      prem  $ natEq n' m'
  ]

-- Less than check (strict)
natLt :: (Redex rel) => L Nat rel -> L Nat rel -> Applied2 rel Nat Nat
natLt = define2 "natLt"
  [ fresh $ \m' ->
      concl $ natLt zro (suc m')
  , fresh2 $ \n' m' -> do
      concl $ natLt (suc n') (suc m')
      prem  $ natLt n' m'
  ]


lookupTm :: (Redex rel) => L Ctx rel -> L Nat rel -> L Ty rel -> Applied3 rel Ctx Nat Ty
lookupTm = define3 "lookupTm"
  [ fresh2 $ \ty rest ->
      concl3' $ lookupTm (tmBind ty rest) zro ty
  , fresh4 $ \ty ty' rest n' -> do
      concl3' $ lookupTm (tmBind ty' rest) (suc n') ty
      prem    $ lookupTm rest n' ty
  , fresh3 $ \rest n ty -> do
      concl3' $ lookupTm (tyBind rest) n ty
      prem    $ lookupTm rest n ty
  ]
        
-- Type substitution: substTy depth subTy ty result
-- Substitutes type variable at index 'depth' with 'subTy' in 'ty'
-- Handles de Bruijn index shifting
substTy :: (Redex rel) => L Nat rel -> L Ty rel -> L Ty rel -> L Ty rel -> Relation rel
substTy = relation4 "substTy" $ \depth subTy ty result ->
  conde
    [ -- Unit stays Unit
      do
        ty <=> tunit
        result <=> tunit
        pure ()
    , -- Variable: check if it's the one to substitute
      fresh $ \n -> do
        ty <=> tvar n
        call $ substTyVar depth subTy n result
        pure ()
    , -- Arrow: substitute in both components
      fresh4 $ \a b a' b' -> do
        ty <=> tarr a b
        call $ substTy depth subTy a a'
        call $ substTy depth subTy b b'
        result <=> tarr a' b'
        pure ()
    , -- Forall: increment depth, substitute in body
      fresh3 $ \body body' depth' -> do
        ty <=> tall body
        depth' <=> suc depth
        call $ substTy depth' subTy body body'
        result <=> tall body'
        pure ()
    ]

-- Helper for substituting type variable
-- If var == depth, substitute; if var > depth, decrement; otherwise keep
substTyVar :: (Redex rel) => L Nat rel -> L Ty rel -> L Nat rel -> L Ty rel -> Relation rel
substTyVar = relation4 "substTyVar" $ \depth subTy n result ->
  conde
    [ -- n == depth: substitute
      do
        prem $ natEq n depth
        result <=> subTy
        pure ()
    , -- n < depth: free variable, keep unchanged
      do
        prem $ natLt n depth
        result <=> tvar n
        pure ()
    , -- n > depth: bound variable from outer scope, decrement
      fresh $ \n' -> do
        prem $ natLt depth n
        n <=> suc n'
        result <=> tvar n'
        pure ()
    ]

-- Shift type variables: shiftTy cutoff amount ty result
-- Increments free variables (>= cutoff) by 'amount'
shiftTy :: (Redex rel) => L Nat rel -> L Nat rel -> L Ty rel -> L Ty rel -> Relation rel
shiftTy = relation4 "shiftTy" $ \cutoff amount ty result ->
  conde
    [ -- Unit
      do
        ty <=> tunit
        result <=> tunit
        pure ()
    , -- Variable: shift if >= cutoff
      fresh $ \n -> do
        ty <=> tvar n
        call $ shiftTyVar cutoff amount n result
        pure ()
    , -- Arrow
      fresh4 $ \a b a' b' -> do
        ty <=> tarr a b
        call $ shiftTy cutoff amount a a'
        call $ shiftTy cutoff amount b b'
        result <=> tarr a' b'
        pure ()
    , -- Forall: increment cutoff
      fresh3 $ \body body' cutoff' -> do
        ty <=> tall body
        cutoff' <=> suc cutoff
        call $ shiftTy cutoff' amount body body'
        result <=> tall body'
        pure ()
    ]

-- Addition for shifting
addNat :: (Redex rel) => L Nat rel -> L Nat rel -> L Nat rel -> Relation rel
addNat = relation3 "addNat" $ \n m sum' ->
  conde
    [ do
        n <=> zro
        sum' <=> m
        pure ()
    , fresh2 $ \n' sum'' -> do
        n <=> suc n'
        sum' <=> suc sum''
        call $ addNat n' m sum''
        pure ()
    ]

shiftTyVar :: (Redex rel) => L Nat rel -> L Nat rel -> L Nat rel -> L Ty rel -> Relation rel
shiftTyVar = relation4 "shiftTyVar" $ \cutoff amount n result ->
  conde
    [ -- n < cutoff: bound variable, keep
      do
        prem $ natLt n cutoff
        result <=> tvar n
        pure ()
    , -- n >= cutoff: free variable, shift
      fresh $ \n' -> do
        -- n >= cutoff means not (n < cutoff)
        -- We check by: either n == cutoff or n > cutoff
        conde
          [ prem $ natEq n cutoff
          , prem $ natLt cutoff n
          ]
        call $ addNat n amount n'
        result <=> tvar n'
        pure ()
    ]

-- Type checking: typeof ctx e ty
-- Γ ⊢ e : A
typeof :: (Redex rel) => L Ctx rel -> L Tm rel -> L Ty rel -> Relation rel
typeof = relation3 "typeof" $ \ctx e ty ->
  conde
    [ -- Unit: Γ ⊢ () : Unit
      do
        e <=> unit'
        ty <=> tunit
        pure ()
    , -- Var: Γ(x) = A ⟹ Γ ⊢ x : A
      fresh $ \n -> do
        e <=> var n
        prem $ lookupTm ctx n ty
        pure ()
    , -- Lam: Γ, x:A ⊢ e : B ⟹ Γ ⊢ λx:A.e : A → B
      fresh3 $ \tyA body tyB -> do
        e <=> lam tyA body
        ty <=> tarr tyA tyB
        call $ typeof (tmBind tyA ctx) body tyB
        pure ()
    , -- App: Γ ⊢ e₁ : A → B, Γ ⊢ e₂ : A ⟹ Γ ⊢ e₁ e₂ : B
      fresh3 $ \e1 e2 tyA -> do
        e <=> app e1 e2
        call $ typeof ctx e1 (tarr tyA ty)
        call $ typeof ctx e2 tyA
        pure ()
    , -- TLam: Γ, α ⊢ e : A ⟹ Γ ⊢ Λα.e : ∀α.A
      fresh2 $ \body tyA -> do
        e <=> tlam body
        ty <=> tall tyA
        call $ typeof (tyBind ctx) body tyA
        pure ()
    , -- TApp: Γ ⊢ e : ∀α.A ⟹ Γ ⊢ e [B] : A[α:=B]
      -- Note: We substitute at depth 0 (the outermost binding)
      fresh4 $ \e' tyB tyA tyA' -> do
        e <=> tapp e' tyB
        call $ typeof ctx e' (tall tyA)
        call $ substTy zro tyB tyA tyA'
        ty <=> tyA'
        pure ()
    ]

-- Run type checking in mode (I,I,O): given ctx and term, find type
typeofIO :: Ctx -> Tm -> Stream Ty
typeofIO ctx0 e0 = runSubstRedex $ fresh $ \ty -> do
  _ <- embed $ typeof (Ground $ project ctx0) (Ground $ project e0) ty
  eval ty

-- Run type checking in mode (I,I,I): verify term has given type
checkIII :: Ctx -> Tm -> Ty -> Stream ()
checkIII ctx0 e0 ty0 = runSubstRedex $ do
  _ <- embed $ typeof (Ground $ project ctx0) (Ground $ project e0) (Ground $ project ty0)
  pure ()

main :: IO ()
main = do
  putStrLn "=== System F Type Checking ==="
  putStrLn ""

  -- Example 1: Unit value
  putStrLn "1. Typecheck: ()"
  putStrLn "   Expected: Unit"
  print $ takeS 1 (typeofIO Nil Unit)
  putStrLn ""

  -- Example 2: Identity function (monomorphic)
  -- λx:Unit. x : Unit → Unit
  let idUnit = Lam TUnit (Var Z)
  putStrLn "2. Typecheck: λx:Unit. x"
  putStrLn "   Expected: Unit → Unit"
  print $ takeS 1 (typeofIO Nil idUnit)
  putStrLn ""

  -- Example 3: Polymorphic identity
  -- Λα. λx:α. x : ∀α. α → α
  let polyId = TLam (Lam (TVar Z) (Var Z))
  putStrLn "3. Typecheck: Λα. λx:α. x"
  putStrLn "   Expected: ∀α. α → α"
  print $ takeS 1 (typeofIO Nil polyId)
  putStrLn ""

  -- Example 4: Apply polymorphic identity to Unit
  -- (Λα. λx:α. x) [Unit] : Unit → Unit
  let polyIdApp = TApp polyId TUnit
  putStrLn "4. Typecheck: (Λα. λx:α. x) [Unit]"
  putStrLn "   Expected: Unit → Unit"
  print $ takeS 1 (typeofIO Nil polyIdApp)
  putStrLn ""

  -- Example 5: Apply polymorphic identity to Unit value
  -- ((Λα. λx:α. x) [Unit]) () : Unit
  let fullApp = App polyIdApp Unit
  putStrLn "5. Typecheck: ((Λα. λx:α. x) [Unit]) ()"
  putStrLn "   Expected: Unit"
  print $ takeS 1 (typeofIO Nil fullApp)
  putStrLn ""

  -- Example 6: Church boolean type: ∀α. α → α → α
  -- True: Λα. λx:α. λy:α. x
  let churchBoolTy = TAll (TArr (TVar Z) (TArr (TVar Z) (TVar Z)))
  let churchTrue = TLam (Lam (TVar Z) (Lam (TVar Z) (Var (S Z))))
  putStrLn "6. Typecheck: Λα. λx:α. λy:α. x  (Church true)"
  putStrLn "   Expected: ∀α. α → α → α"
  print $ takeS 1 (typeofIO Nil churchTrue)
  putStrLn ""

  -- Example 7: Church false: Λα. λx:α. λy:α. y
  let churchFalse = TLam (Lam (TVar Z) (Lam (TVar Z) (Var Z)))
  putStrLn "7. Typecheck: Λα. λx:α. λy:α. y  (Church false)"
  putStrLn "   Expected: ∀α. α → α → α"
  print $ takeS 1 (typeofIO Nil churchFalse)
  putStrLn ""

  -- Example 8: Nested polymorphism
  -- Λα. Λβ. λx:α. λy:β. x : ∀α. ∀β. α → β → α
  let nested = TLam (TLam (Lam (TVar (S Z)) (Lam (TVar Z) (Var (S Z)))))
  putStrLn "8. Typecheck: Λα. Λβ. λx:α. λy:β. x"
  putStrLn "   Expected: ∀α. ∀β. α → β → α"
  print $ takeS 1 (typeofIO Nil nested)
  putStrLn ""

  -- Example 9: Type verification (checking mode)
  putStrLn "9. Verify: (Λα. λx:α. x) : ∀α. α → α"
  let polyIdTy = TAll (TArr (TVar Z) (TVar Z))
  print $ takeS 1 (checkIII Nil polyId polyIdTy)
  putStrLn ""

  -- Example 10: Apply nested polymorphism
  -- (Λα. Λβ. λx:α. λy:β. x) [Unit] [Unit → Unit]
  let nestedApp = TApp (TApp nested TUnit) (TArr TUnit TUnit)
  putStrLn "10. Typecheck: (Λα. Λβ. λx:α. λy:β. x) [Unit] [Unit → Unit]"
  putStrLn "    Expected: Unit → (Unit → Unit) → Unit"
  print $ takeS 1 (typeofIO Nil nestedApp)
  putStrLn ""

  -- Example 11: Self-application type (∀α. α → α) → (∀α. α → α)
  -- λf:(∀α. α → α). f [∀α. α → α] f
  let selfAppTy = TArr polyIdTy polyIdTy
  let selfApp = Lam polyIdTy (App (TApp (Var Z) polyIdTy) (Var Z))
  putStrLn "11. Typecheck: λf:(∀α. α → α). f [∀α. α → α] f"
  putStrLn "    Expected: (∀α. α → α) → (∀α. α → α)"
  print $ takeS 1 (typeofIO Nil selfApp)
  putStrLn ""

  -- Example 12: Term synthesis - find a term of type Unit → Unit
  putStrLn "12. Synthesize term of type Unit → Unit"
  let synthQuery = runSubstRedex $ fresh $ \e -> do
        _ <- embed $ typeof nil e (tarr tunit tunit)
        eval e
  print $ takeS 3 synthQuery
  putStrLn ""

  putStrLn "=== All examples complete ==="
