-- | Rendering helpers shared by interpreters.
module TypedRedex.Render
  ( renderJudgmentCall
  , renderEq
  , renderNeq
  , renderHash
  , renderVarSet
  ) where

import Data.List (intercalate)
import Data.Set (Set)
import qualified Data.Set as S

import TypedRedex.Core.RuleF
import TypedRedex.Pretty (Doc(..), formatJudgment)

renderJudgmentCall :: JudgmentCall name modes ts -> String
renderJudgmentCall jc =
  let docs = renderTermDocs (jcArgs jc)
      Doc rendered = formatJudgment (jcName jc) (jcFormat jc) docs
  in rendered

renderTerm :: Repr a => Term a -> String
renderTerm t =
  displayLogic (termVal t)

renderEq :: Repr a => Term a -> Term a -> String
renderEq t1 t2 = renderTerm t1 ++ " === " ++ renderTerm t2

renderNeq :: Repr a => Term a -> Term a -> String
renderNeq t1 t2 = renderTerm t1 ++ " =/= " ++ renderTerm t2

renderHash :: (Repr name, Repr term) => Term name -> Term term -> String
renderHash name term = renderTerm name ++ " # " ++ renderTerm term

renderVarSet :: Set Int -> String
renderVarSet s =
  case S.toAscList s of
    [] -> "(none)"
    xs -> intercalate " " (map renderVar xs)
  where
    renderVar i = "?" ++ show i

renderTermDocs :: TermList ts -> [Doc]
renderTermDocs TNil = []
renderTermDocs (t :> ts) = Doc (displayLogic (termVal t)) : renderTermDocs ts
