-- | Rule AST: Indexed functor for the free monad DSL
--
-- Pure AST with no interpreter dependencies.
module TypedRedex.Core.RuleF
  ( -- * AST types
    RuleF(..)
  , RuleM
  , Rule(..)
  , Judgment(..)
  , JudgmentCall(..)
  -- * Argument lists
  , TermList(..)
  , PrettyList(..)
  -- * Variable extraction
  , InputVars(..)
  , OutputVars(..)
  -- * Re-exports
  , module TypedRedex.Core.Schedule
  , module TypedRedex.Core.Term
  ) where

import Data.Kind (Type)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Typeable (Typeable)
import GHC.TypeLits (Nat, Symbol, type (+))

import TypedRedex.Core.IxFree (IxFree)
import TypedRedex.Core.Schedule
import TypedRedex.Core.Term
import TypedRedex.Pretty (Doc, Pretty(..), PrettyTerm(..))

--------------------------------------------------------------------------------
-- Argument lists
--------------------------------------------------------------------------------

-- | Typed argument list
data TermList (vss :: [[Nat]]) (ts :: [Type]) where
  TNil :: TermList '[] '[]
  (:>) :: (Repr a, Typeable a) => Term vs a -> TermList vss ts -> TermList (vs ': vss) (a ': ts)
infixr 5 :>

--------------------------------------------------------------------------------
-- Pretty lists
--------------------------------------------------------------------------------

class PrettyList (ts :: [Type]) where
  prettyTermList :: TermList vss ts -> [PrettyTerm]

instance PrettyList '[] where
  prettyTermList TNil = []

instance (Pretty a, PrettyList ts) => PrettyList (a ': ts) where
  prettyTermList (t :> ts) =
    PrettyTerm (termVal t) : prettyTermList ts

--------------------------------------------------------------------------------
-- Variable extraction
--------------------------------------------------------------------------------

class InputVars (ms :: [Mode]) (vss :: [[Nat]]) (ts :: [Type]) where
  inputVars :: ModeList ms -> TermList vss ts -> Set Int

instance InputVars '[] '[] '[] where
  inputVars MNil TNil = S.empty

instance InputVars ms vss ts => InputVars ('I ': ms) (vs ': vss) (t ': ts) where
  inputVars (_ :* ms) (t :> ts) = S.union (termVars t) (inputVars ms ts)

instance InputVars ms vss ts => InputVars ('O ': ms) (vs ': vss) (t ': ts) where
  inputVars (_ :* ms) (_ :> ts) = inputVars ms ts

class OutputVars (ms :: [Mode]) (vss :: [[Nat]]) (ts :: [Type]) where
  outputVars :: ModeList ms -> TermList vss ts -> Set Int

instance OutputVars '[] '[] '[] where
  outputVars MNil TNil = S.empty

instance OutputVars ms vss ts => OutputVars ('I ': ms) (vs ': vss) (t ': ts) where
  outputVars (_ :* ms) (_ :> ts) = outputVars ms ts

instance OutputVars ms vss ts => OutputVars ('O ': ms) (vs ': vss) (t ': ts) where
  outputVars (_ :* ms) (t :> ts) = S.union (termVars t) (outputVars ms ts)

--------------------------------------------------------------------------------
-- Judgment types
--------------------------------------------------------------------------------

-- | A complete rule (existentially hides final state)
data Rule (name :: Symbol) (ts :: [Type]) where
  Rule :: CheckSchedule name steps
       => { ruleName :: String
          , ruleBody :: RuleM ts ('St 0 '[] 'False) ('St n steps 'True) ()
          } -> Rule name ts

-- | A judgment: named collection of rules
data Judgment (name :: Symbol) (modes :: [Mode]) (ts :: [Type]) = Judgment
  { judgmentName  :: String
  , judgmentModes :: ModeList modes
  , judgmentRules :: [Rule name ts]
  , judgmentFormat :: Maybe ([Doc] -> Doc)
  }

-- | A judgment call: judgment applied to arguments
data JudgmentCall (name :: Symbol) (modes :: [Mode]) (vss :: [[Nat]]) (ts :: [Type]) = JudgmentCall
  { jcName     :: String
  , jcModes    :: ModeList modes
  , jcArgs     :: TermList vss ts
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
type RuleM ts s t a = IxFree (RuleF ts) s t a

--------------------------------------------------------------------------------
-- The indexed functor
--------------------------------------------------------------------------------

-- | Indexed functor for rule DSL
--
-- No `rel` parameter — this is pure data.
data RuleF (ts :: [Type]) (s :: St) (t :: St) (a :: Type) where

  -- | Fresh variable (single)
  FreshF :: (Repr a, Typeable a)
         => RuleF ts ('St n steps c) ('St (n + 1) steps c) (Term '[n] a)

  -- | Conclusion
  ConclF :: (InputVars modes vss ts, OutputVars modes vss ts)
         => JudgmentCall name modes vss ts
         -> RuleF ts ('St n steps 'False)
                     ('St n (Snoc steps ('ConcStep name (ReqVars modes vss) (ProdVars modes vss))) 'True) ()

  -- | Premise
  PremF :: (InputVars modes vss ts', OutputVars modes vss ts')
        => JudgmentCall name modes vss ts'
        -> RuleF ts ('St n steps c)
                    ('St n (Snoc steps ('PremStep ('Goal name (ReqVars modes vss) (ProdVars modes vss)))) c) ()

  -- | Negation as failure
  NegF :: Rule name ts'
       -> RuleF ts ('St n steps c)
                   ('St n (Snoc steps ('NegStep '[])) c) ()
       -- TODO: Track required vars in NegStep

  -- | Equality constraint
  EqF :: (Repr a, Typeable a)
      => Term vs1 a -> Term vs2 a
      -> RuleF ts ('St n steps c)
                  ('St n (Snoc steps ('PremStep ('Goal "==" (Union vs1 vs2) '[]))) c) ()

  -- | Disequality constraint
  NEqF :: (Repr a, Typeable a)
       => Term vs1 a -> Term vs2 a
       -> RuleF ts ('St n steps c)
                   ('St n (Snoc steps ('PremStep ('Goal "=/=" (Union vs1 vs2) '[]))) c) ()
