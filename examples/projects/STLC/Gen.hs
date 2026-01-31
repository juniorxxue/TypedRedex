module STLC.Gen
  ( WT(..)
  , genTy
  , genTm
  ) where

import Test.QuickCheck
  ( Arbitrary(..)
  , Gen
  , chooseInt
  , elements
  , frequency
  , sized
  )
import TypedRedex.Nominal.Bind (Bind(..))
import TypedRedex.Nominal.Prelude (Nom(..))

import STLC.Syntax (Ty(..), Tm(..))
import Support.Nat (Nat(..))

-- | A closed, well-typed term paired with its intended type.
data WT = WT
  { wtTy :: Ty
  , wtTm :: Tm
  }
  deriving (Eq, Show)

instance Arbitrary WT where
  arbitrary = sized $ \n -> do
    ty <- genTy (max 0 (n `div` 2))
    (tm, _) <- genTm n [] 0 ty
    pure (WT ty tm)

genTy :: Int -> Gen Ty
genTy n
  | n <= 0 = elements [TyInt, TyBool]
  | otherwise =
      frequency
        [ (4, elements [TyInt, TyBool])
        , (1, TyArr <$> genTy (n - 1) <*> genTy (n - 1))
        ]

genNat :: Int -> Gen Nat
genNat n = natFromInt <$> chooseInt (0, max 0 (min 6 (n + 1)))

natFromInt :: Int -> Nat
natFromInt k
  | k <= 0 = Z
  | otherwise = S (natFromInt (k - 1))

varsOfType :: Ty -> [(Nom, Ty)] -> [Nom]
varsOfType ty env = [x | (x, ty') <- env, ty' == ty]

genValue :: Int -> [(Nom, Ty)] -> Int -> Ty -> Gen (Tm, Int)
genValue n env next ty =
  case ty of
    TyInt -> do
      k <- genNat n
      pure (Lit k, next)
    TyBool -> elements [(BTrue, next), (BFalse, next)]
    TyArr a b -> do
      let x = Nom next
      (body, next') <- genTm (max 0 (n - 1)) ((x, a) : env) (next + 1) b
      pure (Lam a (Bind x body), next')

-- | Closed term generator threaded with:
--   (1) a typing environment of in-scope variables, and
--   (2) a fresh-name supply for binders.
genTm :: Int -> [(Nom, Ty)] -> Int -> Ty -> Gen (Tm, Int)
genTm n env next ty
  | n <= 0 = genBase env next ty
  | otherwise =
      frequency (generalChoices ++ tyChoices ++ varChoices ++ redexChoices)
  where
    varChoices =
      case varsOfType ty env of
        [] -> []
        xs ->
          [ (3, do
              x <- elements xs
              pure (TmVar x, next)
            )
          ]

    genLit = do
      k <- genNat n
      pure (Lit k, next)

    genBool =
      elements [(BTrue, next), (BFalse, next)]

    genLam :: Ty -> Ty -> Gen (Tm, Int)
    genLam a b = do
      let x = Nom next
      (body, next') <- genTm (n - 1) ((x, a) : env) (next + 1) b
      pure (Lam a (Bind x body), next')

    genApp = do
      argTy <- genTy (max 0 (n `div` 3))
      (t1, next1) <- genTm (n `div` 2) env next (TyArr argTy ty)
      (t2, next2) <- genTm (n `div` 2) env next1 argTy
      pure (App t1 t2, next2)

    genIf = do
      (c, next1) <- genTm (n `div` 3) env next TyBool
      (t, next2) <- genTm (n `div` 3) env next1 ty
      (e, next3) <- genTm (n `div` 3) env next2 ty
      pure (If c t e, next3)

    genPlus = do
      (t1, next1) <- genTm (n `div` 2) env next TyInt
      (t2, next2) <- genTm (n `div` 2) env next1 TyInt
      pure (Plus t1 t2, next2)

    -- Force-generation of concrete redexes so we reliably test reduction rules.
    redexChoices =
      [ (2, genIfRedex)
      , (2, genBetaRedex)
      ]
        ++ case ty of
             TyInt -> [(2, genDeltaRedex)]
             _ -> []

    genIfRedex = do
      (t, next1) <- genTm (n `div` 2) env next ty
      (e, next2) <- genTm (n `div` 2) env next1 ty
      b <- elements [BTrue, BFalse]
      pure (If b t e, next2)

    genDeltaRedex = do
      k1 <- genNat n
      k2 <- genNat n
      pure (Plus (Lit k1) (Lit k2), next)

    genBetaRedex = do
      argTy <- genTy (max 0 (n `div` 3))
      let x = Nom next
      (body, next1) <- genTm (n `div` 2) ((x, argTy) : env) (next + 1) ty
      (v, next2) <- genValue (n `div` 3) env next1 argTy
      pure (App (Lam argTy (Bind x body)) v, next2)

    generalChoices =
      [ (2, genIf)
      , (2, genApp)
      ]

    tyChoices =
      case ty of
        TyInt -> [(4, genLit), (2, genPlus)]
        TyBool -> [(4, genBool)]
        TyArr a b -> [(5, genLam a b)]

genBase :: [(Nom, Ty)] -> Int -> Ty -> Gen (Tm, Int)
genBase env next ty =
  case ty of
    TyInt -> do
      n <- genNat 0
      pure (Lit n, next)
    TyBool ->
      elements [(BTrue, next), (BFalse, next)]
    TyArr a b -> do
      let x = Nom next
      (body, next') <- genTm 0 ((x, a) : env) (next + 1) b
      pure (Lam a (Bind x body), next')

