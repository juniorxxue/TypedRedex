-- | Rule AST: Indexed functor for the free monad DSL
--
-- Pure AST with no interpreter dependencies.
module TypedRedex.Core.RuleF
  ( -- * AST types
    RuleF(..)
  , RuleM
  , Rule(..)
  , JudgmentDef(..)
  , JudgmentCall(..)
  -- * Argument lists
  , TermList(..)
  , PrettyList(..)
  -- * Variable extraction
  , inputVars
  , outputVars
  -- * Re-exports
  , module TypedRedex.Core.Schedule
  , module TypedRedex.Core.Term
  ) where

import Data.Kind (Type)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Typeable (Typeable)
import GHC.TypeLits (Symbol)

import TypedRedex.Core.IxFree (IxFree)
import TypedRedex.Core.Schedule
import TypedRedex.Core.Term
import TypedRedex.Pretty (Doc, Pretty(..), PrettyTerm(..))
import TypedRedex.Nominal (NominalAtom, Hash, FreshName)

--------------------------------------------------------------------------------
-- Argument lists
--------------------------------------------------------------------------------

-- | Typed argument list
data TermList (ts :: [Type]) where
  TNil :: TermList '[]
  (:>) :: (Repr a, Typeable a) => Term a -> TermList ts -> TermList (a ': ts)
infixr 5 :>

--------------------------------------------------------------------------------
-- Pretty lists
--------------------------------------------------------------------------------

class PrettyList (ts :: [Type]) where
  prettyTermList :: TermList ts -> [PrettyTerm]

instance PrettyList '[] where
  prettyTermList TNil = []

instance (Pretty a, PrettyList ts) => PrettyList (a ': ts) where
  prettyTermList (t :> ts) = PrettyTerm (termVal t) : prettyTermList ts

--------------------------------------------------------------------------------
-- Variable extraction
--------------------------------------------------------------------------------

inputVars :: ModeList modes -> TermList ts -> Set Int
inputVars MNil TNil = S.empty
inputVars (I :* ms) (t :> ts) = S.union (termVars t) (inputVars ms ts)
inputVars (O :* ms) (_ :> ts) = inputVars ms ts
inputVars _ _ = error "inputVars: mode/argument length mismatch"

outputVars :: ModeList modes -> TermList ts -> Set Int
outputVars MNil TNil = S.empty
outputVars (I :* ms) (_ :> ts) = outputVars ms ts
outputVars (O :* ms) (t :> ts) = S.union (termVars t) (outputVars ms ts)
outputVars _ _ = error "outputVars: mode/argument length mismatch"

--------------------------------------------------------------------------------
-- Judgment definitions
--------------------------------------------------------------------------------

-- | A complete rule (existentially hides final state)
data Rule (name :: Symbol) (ts :: [Type]) = Rule
  { ruleName :: String
  , ruleBody :: RuleM ts ()
  }

-- | A judgment definition: named collection of rules
data JudgmentDef (name :: Symbol) (modes :: [Mode]) (ts :: [Type]) = JudgmentDef
  { judgmentName  :: String
  , judgmentModes :: ModeList modes
  , judgmentRules :: [Rule name ts]
  , judgmentFormat :: Maybe ([Doc] -> Doc)
  }

-- | A judgment call: judgment applied to arguments
data JudgmentCall (name :: Symbol) (modes :: [Mode]) (ts :: [Type]) = JudgmentCall
  { jcName     :: String
  , jcModes    :: ModeList modes
  , jcArgs     :: TermList ts
  , jcReqVars  :: Set Int
  , jcProdVars :: Set Int
  , jcRules    :: [Rule name ts]
  , jcFormat   :: Maybe ([Doc] -> Doc)
  , jcPretty   :: [PrettyTerm]
  }

--------------------------------------------------------------------------------
-- Rule monad
--------------------------------------------------------------------------------

-- | The rule monad: indexed free monad over RuleF
type RuleM ts a = IxFree (RuleF ts) () () a

--------------------------------------------------------------------------------
-- The indexed functor
--------------------------------------------------------------------------------

-- | Indexed functor for rule DSL
--
-- No `rel` parameter — this is pure data.
data RuleF (ts :: [Type]) s t (a :: Type) where

  -- | Fresh variable (single)
  FreshF :: (Repr a, Typeable a)
         => RuleF ts s s (Term a)

  -- | Fresh nominal atom (ground name)
  FreshNameF :: (NominalAtom name, FreshName name, Repr name, Typeable name)
             => RuleF ts s s (Term name)

  -- | Guard block.
  --
  -- Guards are executed before normal premises/constraints, and multiple guards
  -- run in source order. This is useful to force an imperative order when mode
  -- analysis cannot infer one.
  GuardF :: RuleM ts ()
         -> RuleF ts s s ()

  -- | Conclusion
  ConclF :: JudgmentCall name modes ts
         -> RuleF ts s s ()

  -- | Premise
  PremF :: JudgmentCall name modes ts'
        -> RuleF ts s s ()

  -- | Negation as failure
  NegF :: Rule name ts'
       -> RuleF ts s s ()

  -- | Equality constraint
  EqF :: (Repr a, Typeable a, Pretty a)
      => Term a -> Term a
      -> RuleF ts s s ()

  -- | Disequality constraint
  NEqF :: (Repr a, Typeable a, Pretty a)
      => Term a -> Term a
      -> RuleF ts s s ()

  -- | Freshness (hash) constraint: name # term
  HashF :: (NominalAtom name, Hash name term, Repr name, Repr term, Typeable name, Typeable term, Pretty name, Pretty term)
        => Term name -> Term term
        -> RuleF ts s s ()
