-- | Query builder and extraction utilities.
module TypedRedex.Backend.Query
  ( Query(..)
  , SomeJudgmentCall(..)
  , query
  , QueryM
  , qfresh
  ) where

import Control.Monad.State.Strict (State, evalState, get, put)
import Data.Kind (Type)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Typeable (Typeable)

import TypedRedex.Backend.Engine (SomeJudgmentCall(..), checkQueryInputs, translate)
import TypedRedex.Backend.Goal
  ( Goal
  , Subst
  , applySubstLogic
  )
import TypedRedex.Core.RuleF

-- | A query to execute.
data Query a = Query
  { queryGoal     :: Goal
  , queryNextVar  :: Int
  , queryExtract  :: Subst -> Maybe a
  , queryCall     :: SomeJudgmentCall
  }

--------------------------------------------------------------------------------
-- Query builder
--------------------------------------------------------------------------------

-- | Query-building monad with fresh logic variables.
newtype QueryM a = QueryM (State Int a)
  deriving (Functor, Applicative, Monad)

-- | Allocate a fresh query variable.
qfresh :: forall a. (Repr a, Typeable a) => QueryM (Term a)
qfresh = QueryM $ do
  i <- get
  put (i + 1)
  pure (Term (S.singleton i) (Var i))

-- | Build a query from a judgment call and output spec.
query :: forall out name modes ts.
         (Extract out, CollectVars out)
      => QueryM (JudgmentCall name modes ts, out)
      -> Query (Out out)
query qm =
  let (result, nextVar) = runQueryState qm
      (jc, outSpec) = result
      varsInCall = varsTermList (jcArgs jc)
      varsInOut  = collectVars outSpec
      maxVar     = maxVarId (S.union varsInCall varsInOut)
      nextVar'   = max nextVar (maxVar + 1)
      goal       = translate jc
      extractFn  = \s -> extractOut s outSpec
  in case checkQueryInputs jc of
       Nothing ->
         Query
           { queryGoal = goal
           , queryNextVar = nextVar'
           , queryExtract = extractFn
           , queryCall = SomeJudgmentCall jc
           }
       Just err -> error err
  where
    runQueryState :: QueryM a -> (a, Int)
    runQueryState (QueryM st) = evalState ((,) <$> st <*> get) 0

--------------------------------------------------------------------------------
-- Output extraction
--------------------------------------------------------------------------------

class Extract a where
  type Out a :: Type
  extractOut :: Subst -> a -> Maybe (Out a)

instance (Repr a, Typeable a) => Extract (Term a) where
  type Out (Term a) = a
  extractOut s t = evalTerm s t

instance (Extract a, Extract b) => Extract (a, b) where
  type Out (a, b) = (Out a, Out b)
  extractOut s (a, b) = (,) <$> extractOut s a <*> extractOut s b

instance (Extract a, Extract b, Extract c) => Extract (a, b, c) where
  type Out (a, b, c) = (Out a, Out b, Out c)
  extractOut s (a, b, c) = (,,) <$> extractOut s a <*> extractOut s b <*> extractOut s c

instance (Extract a, Extract b, Extract c, Extract d) => Extract (a, b, c, d) where
  type Out (a, b, c, d) = (Out a, Out b, Out c, Out d)
  extractOut s (a, b, c, d) =
    (,,,) <$> extractOut s a <*> extractOut s b <*> extractOut s c <*> extractOut s d

instance (Extract a, Extract b, Extract c, Extract d, Extract e) => Extract (a, b, c, d, e) where
  type Out (a, b, c, d, e) = (Out a, Out b, Out c, Out d, Out e)
  extractOut s (a, b, c, d, e) =
    (,,,,) <$> extractOut s a <*> extractOut s b <*> extractOut s c <*> extractOut s d <*> extractOut s e

evalTerm :: (Repr a, Typeable a) => Subst -> Term a -> Maybe a
evalTerm s (Term _ l) =
  case applySubstLogic s l of
    Var _      -> Nothing
    Ground r -> reify r

--------------------------------------------------------------------------------
-- Variable collection helpers
--------------------------------------------------------------------------------

class CollectVars a where
  collectVars :: a -> Set Int

instance CollectVars (Term a) where
  collectVars = termVars

instance (CollectVars a, CollectVars b) => CollectVars (a, b) where
  collectVars (a, b) = S.union (collectVars a) (collectVars b)

instance (CollectVars a, CollectVars b, CollectVars c) => CollectVars (a, b, c) where
  collectVars (a, b, c) = S.unions [collectVars a, collectVars b, collectVars c]

instance (CollectVars a, CollectVars b, CollectVars c, CollectVars d) => CollectVars (a, b, c, d) where
  collectVars (a, b, c, d) = S.unions [collectVars a, collectVars b, collectVars c, collectVars d]

instance (CollectVars a, CollectVars b, CollectVars c, CollectVars d, CollectVars e) => CollectVars (a, b, c, d, e) where
  collectVars (a, b, c, d, e) =
    S.unions [collectVars a, collectVars b, collectVars c, collectVars d, collectVars e]

varsTermList :: TermList ts -> Set Int
varsTermList TNil = S.empty
varsTermList (t :> ts) = S.union (termVars t) (varsTermList ts)

maxVarId :: Set Int -> Int
maxVarId s
  | S.null s = -1
  | otherwise = S.foldl' max (-1) s
