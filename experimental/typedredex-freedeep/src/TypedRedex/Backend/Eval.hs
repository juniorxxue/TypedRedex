-- | Eval interpreter: execute queries via miniKanren.
module TypedRedex.Backend.Eval
  ( -- * Query execution
    eval
  , Query(..)
  , SomeJudgmentCall(..)
  , query
  , QueryM
  , qfresh
    -- * Translation
  , translate
  , translateRuleClosed
  ) where

import Data.Maybe (mapMaybe)

import TypedRedex.Backend.Engine (SomeJudgmentCall(..), translate, translateRuleClosed)
import TypedRedex.Backend.Goal (Subst(..), emptySubst, exec)
import TypedRedex.Backend.Query (Query(..), query, QueryM, qfresh)

-- | Evaluate a query.
eval :: Query a -> [a]
eval q =
  let startSubst = emptySubst { substNextVar = queryNextVar q }
  in mapMaybe (queryExtract q) (exec (queryGoal q) startSubst)
