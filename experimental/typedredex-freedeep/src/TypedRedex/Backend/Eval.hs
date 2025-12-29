-- | Eval interpreter: execute queries via miniKanren
--
-- Placeholder: Translation defined, full execution not implemented.
module TypedRedex.Backend.Eval
  ( -- * Query execution (placeholder)
    eval
  , Query(..)
  -- * Translation (placeholder)
  , translate
  ) where

import TypedRedex.Core.RuleF (Rule(..))
import TypedRedex.Backend.Goal (Goal(..))

-- | A query to execute
data Query a = Query
  { queryJudgment :: String
  , queryGoal     :: Goal
  -- TODO: track output variables for result extraction
  }

-- | Evaluate a query (placeholder)
--
-- Returns list of results. Currently returns empty list.
eval :: Query a -> [a]
eval _q = []  -- TODO: execute and extract results
  -- let substs = exec (queryGoal q) emptySubst
  -- in map (extractResult q) substs

-- | Translate a rule to a Goal (placeholder)
translate :: Rule ts -> Goal
translate (Rule _name _body) = undefined  -- TODO: fold over RuleM
