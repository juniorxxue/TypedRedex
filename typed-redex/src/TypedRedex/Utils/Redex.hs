{-# LANGUAGE Rank2Types #-}

-- | TypedRedex utilities module.
--
-- This module re-exports from the focused utility modules:
--
-- * "TypedRedex.Utils.Fresh" - fresh variable allocation
-- * "TypedRedex.Utils.Relation" - relation construction and invocation
-- * "TypedRedex.Utils.Run" - relation execution
-- * "TypedRedex.Utils.Format" - term formatting
-- * "TypedRedex.Core.Internal.Unify" - unification helpers (for interpreters)
--
-- This module is kept for backward compatibility. New code should import
-- from the specific modules directly.
module TypedRedex.Utils.Redex
  ( -- * Type aliases (from Fresh)
    Var', L
    -- * Fresh variable allocation (from Fresh)
  , fresh, fresh2, fresh3, fresh4, fresh5
  , argument, argument2, argument3, argument4, argument5
    -- * Relation construction (from Relation)
  , relation, relation2, relation3, relation4, relation5
  , call, premise, embed
  , (===), (<=>)
  , conde
    -- * Evaluation (from Run)
  , eval
  , run, run2, run3, run4, run5
    -- * Formatting (from Format)
  , formatCon
  , prettyLogic
  , intercalate
  , subscriptNum
    -- * Unification helpers (from Unify, for interpreters)
  , flatteningUnify
  , occursCheck
  , evalFromRead
    -- * Re-exports
  , neg  -- from Redex typeclass
  ) where

-- Re-export from focused modules
import TypedRedex.Utils.Fresh
import TypedRedex.Utils.Relation
import TypedRedex.Utils.Run
import TypedRedex.Utils.Format
import TypedRedex.Core.Internal.Unify
import TypedRedex.Core.Internal.Redex (neg)
