-- | Typeset interpreter: pretty-print rules as inference rules
--
-- Direct AST traversal, no execution.
module TypedRedex.Interp.Typeset
  ( typeset
  , typesetRule
  , typesetTermList
  ) where

import Data.List (intercalate)
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
typesetRule :: Rule ts -> String
typesetRule (Rule name body) =
  let (premises, conclusion, constraints) = extractRule body
  in unlines
       [ "[" ++ name ++ "]"
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
            dummyTerm = Term mempty (Var varId)
        in go (k dummyTerm) ex'

      Fresh2F ->
        let v0 = exNextVar ex
            ex' = ex { exNextVar = v0 + 2 }
            t0 = Term mempty (Var v0)
            t1 = Term mempty (Var (v0 + 1))
        in go (k (t0, t1)) ex'

      Fresh3F ->
        let v0 = exNextVar ex
            ex' = ex { exNextVar = v0 + 3 }
            t0 = Term mempty (Var v0)
            t1 = Term mempty (Var (v0 + 1))
            t2 = Term mempty (Var (v0 + 2))
        in go (k (t0, t1, t2)) ex'

      Fresh4F ->
        let v0 = exNextVar ex
            ex' = ex { exNextVar = v0 + 4 }
            t0 = Term mempty (Var v0)
            t1 = Term mempty (Var (v0 + 1))
            t2 = Term mempty (Var (v0 + 2))
            t3 = Term mempty (Var (v0 + 3))
        in go (k (t0, t1, t2, t3)) ex'

      Fresh5F ->
        let v0 = exNextVar ex
            ex' = ex { exNextVar = v0 + 5 }
            t0 = Term mempty (Var v0)
            t1 = Term mempty (Var (v0 + 1))
            t2 = Term mempty (Var (v0 + 2))
            t3 = Term mempty (Var (v0 + 3))
            t4 = Term mempty (Var (v0 + 4))
        in go (k (t0, t1, t2, t3, t4)) ex'

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

formatNegRule :: Rule ts -> String
formatNegRule (Rule name _) = name ++ "..."

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
