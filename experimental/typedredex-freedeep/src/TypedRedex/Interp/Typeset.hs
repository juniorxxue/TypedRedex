-- | Typeset interpreter: pretty-print rules as inference rules
--
-- Direct AST traversal, no execution.
module TypedRedex.Interp.Typeset
  ( typeset
  , typesetRule
  , typesetTermList
  ) where

import Data.List (intercalate)
import qualified Data.Set as S
import TypedRedex.Core.IxFree (IxFree(..))
import TypedRedex.Core.RuleF
import TypedRedex.Pretty

--------------------------------------------------------------------------------
-- Main interface
--------------------------------------------------------------------------------

-- | Typeset all rules for a judgment call
typeset :: JudgmentCall name modes vss ts -> String
typeset jc = unlines
  [ "Judgment: " ++ jcName jc
  , replicate 40 '-'
  , unlines (map typesetRule (jcRules jc))
  ]

-- | Typeset a single rule
typesetRule :: Rule name ts -> String
typesetRule (Rule ruleLabel body) =
  let (premises, conclusion, constraints) = extractRule body
      ((premDocs, conclDoc, constraintDocs), _) =
        runPrettyWith emptyPrettyCtx (renderExtracted premises conclusion constraints)
      premLine = if null premDocs then "" else intercalate "    " (map renderDoc premDocs)
      conclLine = renderDoc conclDoc
      constraintLine =
        case constraintDocs of
          [] -> ""
          cs -> "  [" ++ intercalate ", " (map renderDoc cs) ++ "]"
  in unlines
       [ "[" ++ ruleLabel ++ "]"
       , ""
       , formatInferenceRule premLine conclLine constraintLine
       ]

--------------------------------------------------------------------------------
-- Rule extraction
--------------------------------------------------------------------------------

data Premise where
  Premise :: JudgmentCall name modes vss ts -> Premise

data Constraint where
  EqC  :: Pretty a => Term vs1 a -> Term vs2 a -> Constraint
  NeqC :: Pretty a => Term vs1 a -> Term vs2 a -> Constraint
  NegC :: String -> Constraint

data Extracted = Extracted
  { exPremises    :: [Premise]
  , exConclusion  :: Maybe Premise
  , exConstraints :: [Constraint]
  , exNextVar     :: Int
  }

emptyExtracted :: Extracted
emptyExtracted = Extracted [] Nothing [] 0

extractRule :: RuleM ts s t a -> ([Premise], Premise, [Constraint])
extractRule body =
  let ex = go body emptyExtracted
  in (exPremises ex, maybe (Premise (error "missing conclusion")) id (exConclusion ex), exConstraints ex)
  where
    go :: RuleM ts s' t' a -> Extracted -> Extracted
    go (Pure _) ex = ex
    go (Bind op k) ex = case op of
      FreshF ->
        let varId = exNextVar ex
            ex' = ex { exNextVar = varId + 1 }
            dummyTerm = Term (S.singleton varId) (Var varId)
        in go (k dummyTerm) ex'

      ConclF jc ->
        go (k ()) ex { exConclusion = Just (Premise jc) }

      PremF jc ->
        go (k ()) ex { exPremises = exPremises ex ++ [Premise jc] }

      NegF innerRule ->
        let neg = NegC (formatNegRule innerRule)
        in go (k ()) ex { exConstraints = exConstraints ex ++ [neg] }

      EqF t1 t2 ->
        go (k ()) ex { exConstraints = exConstraints ex ++ [EqC t1 t2] }

      NEqF t1 t2 ->
        go (k ()) ex { exConstraints = exConstraints ex ++ [NeqC t1 t2] }

formatNegRule :: Rule name ts -> String
formatNegRule (Rule ruleLabel _) = ruleLabel ++ "..."

--------------------------------------------------------------------------------
-- Term list display
--------------------------------------------------------------------------------

typesetTermList :: PrettyList ts => TermList vss ts -> String
typesetTermList tl =
  let (docs, _) = runPrettyWith emptyPrettyCtx (renderTermList tl)
  in renderDoc (commaSep docs)

--------------------------------------------------------------------------------
-- Formatting
--------------------------------------------------------------------------------

formatInferenceRule :: String -> String -> String -> String
formatInferenceRule premLine conclusion constraintLine =
  let width = max (length conclusion) (length premLine)
      bar = replicate width '-'
  in unlines $ filter (not . null)
       [ premLine
       , bar ++ constraintLine
       , conclusion
       ]

--------------------------------------------------------------------------------
-- Rendering
--------------------------------------------------------------------------------

renderExtracted
  :: [Premise]
  -> Premise
  -> [Constraint]
  -> PrettyM ([Doc], Doc, [Doc])
renderExtracted premises conclusion constraints = do
  conclDoc <- renderPremise conclusion
  premDocs <- mapM renderPremise premises
  constraintDocs <- mapM renderConstraint constraints
  pure (premDocs, conclDoc, constraintDocs)

renderPremise :: Premise -> PrettyM Doc
renderPremise (Premise jc) = do
  args <- mapM prettyTermDoc (jcPretty jc)
  pure (formatJudgment (jcName jc) (jcFormat jc) args)

renderConstraint :: Constraint -> PrettyM Doc
renderConstraint (EqC t1 t2) = do
  d1 <- prettyTerm t1
  d2 <- prettyTerm t2
  pure (d1 <+> Doc " = " <+> d2)
renderConstraint (NeqC t1 t2) = do
  d1 <- prettyTerm t1
  d2 <- prettyTerm t2
  pure (d1 <+> Doc " =/= " <+> d2)
renderConstraint (NegC name) =
  pure (Doc "not(" <> Doc name <> Doc ")")

renderTermList :: PrettyList ts => TermList vss ts -> PrettyM [Doc]
renderTermList tl = mapM prettyTermDoc (prettyTermList tl)
