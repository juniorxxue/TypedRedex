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
import TypedRedex.Core.Term
import TypedRedex.Core.RuleF

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
  in unlines
       [ "[" ++ ruleLabel ++ "]"
       , ""
       , formatInferenceRule premises conclusion constraints
       ]

--------------------------------------------------------------------------------
-- Rule extraction
--------------------------------------------------------------------------------

data Extracted = Extracted
  { exPremises    :: [String]
  , exConclusion  :: Maybe String
  , exConstraints :: [String]
  , exNextVar     :: Int
  }

emptyExtracted :: Extracted
emptyExtracted = Extracted [] Nothing [] 0

extractRule :: RuleM ts s t a -> ([String], String, [String])
extractRule body =
  let ex = go body emptyExtracted
  in (exPremises ex, maybe "?" id (exConclusion ex), exConstraints ex)
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
        let concl = jcName jc ++ "(" ++ typesetTermList (jcArgs jc) ++ ")"
        in go (k ()) ex { exConclusion = Just concl }

      PremF jc ->
        let prem = jcName jc ++ "(" ++ typesetTermList (jcArgs jc) ++ ")"
        in go (k ()) ex { exPremises = exPremises ex ++ [prem] }

      NegF innerRule ->
        let neg = "¬(" ++ formatNegRule innerRule ++ ")"
        in go (k ()) ex { exConstraints = exConstraints ex ++ [neg] }

      EqF t1 t2 ->
        let eq = displayTerm t1 ++ " = " ++ displayTerm t2
        in go (k ()) ex { exConstraints = exConstraints ex ++ [eq] }

      NEqF t1 t2 ->
        let neq = displayTerm t1 ++ " ≠ " ++ displayTerm t2
        in go (k ()) ex { exConstraints = exConstraints ex ++ [neq] }

formatNegRule :: Rule name ts -> String
formatNegRule (Rule ruleLabel _) = ruleLabel ++ "..."

displayTerm :: Repr a => Term vs a -> String
displayTerm (Term _ val) = displayLogic val

--------------------------------------------------------------------------------
-- Term list display
--------------------------------------------------------------------------------

typesetTermList :: TermList vss ts -> String
typesetTermList = intercalate ", " . go
  where
    go :: TermList vss ts -> [String]
    go TNil = []
    go (t :> ts) = displayTerm t : go ts

--------------------------------------------------------------------------------
-- Formatting
--------------------------------------------------------------------------------

formatInferenceRule :: [String] -> String -> [String] -> String
formatInferenceRule premises conclusion constraints =
  let premLine = if null premises then "" else intercalate "    " premises
      width = max (length conclusion) (length premLine)
      bar = replicate width '─'
      constraintLine = if null constraints
                       then ""
                       else "  [" ++ intercalate ", " constraints ++ "]"
  in unlines $ filter (not . null)
       [ premLine
       , bar ++ constraintLine
       , conclusion
       ]
