module STLC.Properties
  ( qcArgs
  , prop_progress
  , prop_preservation
  ) where

import Test.QuickCheck
  ( Args(..)
  , Property
  , classify
  , conjoin
  , counterexample
  , cover
  , stdArgs
  , tabulate
  )
import TypedRedex.Backend.Eval (eval, query, qfresh)
import TypedRedex.Core.Term (ground)
import TypedRedex.Nominal.Bind (Bind(..))
import TypedRedex.Pretty (Doc(..), prettyGround)

import STLC.Gen (WT(..))
import STLC.Rules (step, typeof)
import STLC.Syntax (Ty(..), Tm(..), eempty)

--------------------------------------------------------------------------------
-- Relational interface (run judgments on ground terms)
--------------------------------------------------------------------------------

infer0 :: Tm -> [Ty]
infer0 tm =
  eval $ query $ do
    ty <- qfresh
    pure (typeof eempty (ground tm) ty, ty)

step1 :: Tm -> [Tm]
step1 tm =
  eval $ query $ do
    tm' <- qfresh
    pure (step (ground tm) tm', tm')

--------------------------------------------------------------------------------
-- Small helpers (for good failure messages + coverage)
--------------------------------------------------------------------------------

ppTm :: Tm -> String
ppTm = renderDoc . prettyGround

ppTy :: Ty -> String
ppTy = renderDoc . prettyGround

isValue :: Tm -> Bool
isValue tm =
  case tm of
    Lit _ -> True
    BTrue -> True
    BFalse -> True
    Lam _ _ -> True
    _ -> False

walkTm :: (Tm -> Bool) -> Tm -> Bool
walkTm p tm =
  p tm
    || case tm of
         Lam _ (Bind _ b) -> walkTm p b
         App t1 t2 -> walkTm p t1 || walkTm p t2
         Plus t1 t2 -> walkTm p t1 || walkTm p t2
         If c t e -> walkTm p c || walkTm p t || walkTm p e
         _ -> False

tag :: Tm -> String
tag t =
  case t of
    TmVar{} -> "Var"
    Lit{} -> "Lit"
    Lam{} -> "Lam"
    App{} -> "App"
    Plus{} -> "Plus"
    BTrue -> "True"
    BFalse -> "False"
    If{} -> "If"

hasBetaRedex :: Tm -> Bool
hasBetaRedex =
  walkTm $ \tm ->
    case tm of
      App (Lam _ _) v | isValue v -> True
      _ -> False

hasDeltaRedex :: Tm -> Bool
hasDeltaRedex =
  walkTm $ \tm ->
    case tm of
      Plus (Lit _) (Lit _) -> True
      _ -> False

hasIfRedex :: Tm -> Bool
hasIfRedex =
  walkTm $ \tm ->
    case tm of
      If BTrue _ _ -> True
      If BFalse _ _ -> True
      _ -> False

withCoverage :: Tm -> Property -> Property
withCoverage tm =
  tabulate "top" [tag tm]
    . classify (isValue tm) "value"
    . classify (not (isValue tm)) "non-value"
    . cover 25 (not (isValue tm)) "non-value(>=25%)"
    . cover 10 (hasBetaRedex tm) "has-β(>=10%)"
    . cover 10 (hasDeltaRedex tm) "has-δ+(>=10%)"
    . cover 10 (hasIfRedex tm) "has-ifT/F(>=10%)"

checkWellTyped :: WT -> (Ty -> Tm -> Property) -> Property
checkWellTyped (WT expected tm) k =
  case infer0 tm of
    [] ->
      counterexample ("Expected well-typed term, got no types.\nterm: " ++ ppTm tm) False
    [ty]
      | ty == expected -> k ty tm
      | otherwise ->
          counterexample
            (unlines
              [ "Generator/typechecker mismatch."
              , "expected type: " ++ ppTy expected
              , "inferred type: " ++ ppTy ty
              , "term: " ++ ppTm tm
              ])
            False
    tys ->
      counterexample
        (unlines
          [ "Multiple types inferred (expected determinism)."
          , "types: " ++ show (map ppTy tys)
          , "term: " ++ ppTm tm
          ])
        False

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

prop_progress :: WT -> Property
prop_progress wt =
  checkWellTyped wt $ \ty tm ->
    let ok = isValue tm || not (null (step1 tm))
    in withCoverage tm $
        counterexample
          (unlines
            [ "Progress failed."
            , "type: " ++ ppTy ty
            , "term: " ++ ppTm tm
            ])
          ok

prop_preservation :: WT -> Property
prop_preservation wt =
  checkWellTyped wt $ \ty tm ->
    let checkOne tm' =
          let tys' = infer0 tm'
          in counterexample
              (unlines
                [ "Preservation failed."
                , "type: " ++ ppTy ty
                , "term: " ++ ppTm tm
                , "stepped to: " ++ ppTm tm'
                , "types of stepped term: " ++ show (map ppTy tys')
                ])
              (tys' == [ty])
    in withCoverage tm $
        conjoin (map checkOne (step1 tm))

--------------------------------------------------------------------------------
-- Default QuickCheck settings
--------------------------------------------------------------------------------

qcArgs :: Args
qcArgs = stdArgs { maxSuccess = 500, maxSize = 22 }
