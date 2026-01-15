-- | MiniKanren Goal AST (deeply embedded)
--
-- Placeholder: Types defined, execution not implemented.
module TypedRedex.Backend.Goal
  ( -- * Goal AST
    Goal(..)
  , VarId(..)
  , logicVar
  -- * Substitution
  , Subst(..)
  , SomeBinding(..)
  , emptySubst
  , walkLogic
  , applySubstLogic
  -- * Execution (placeholder)
  , exec
  ) where

import Data.Typeable (Typeable, cast)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import TypedRedex.Core.Term (Logic, Repr)
import qualified TypedRedex.Core.Term as Term

-- | Typed variable ID
newtype VarId a = VarId Int
  deriving (Eq, Show)

-- | Goal AST (deeply embedded)
data Goal where
  Fresh    :: (Repr a, Typeable a) => (VarId a -> Goal) -> Goal
  Unify    :: (Repr a, Typeable a) => Logic a -> Logic a -> Goal
  Disunify :: (Repr a, Typeable a) => Logic a -> Logic a -> Goal
  Conj     :: Goal -> Goal -> Goal
  Disj     :: Goal -> Goal -> Goal
  Neg      :: Goal -> Goal
  Success  :: Goal
  Failure  :: Goal

-- | Existential binding
data SomeBinding where
  SomeBinding :: (Repr a, Typeable a) => Logic a -> SomeBinding

-- | Substitution: map from var IDs to bindings
data Subst = Subst
  { substBindings :: IntMap SomeBinding
  , substNextVar  :: Int
  }

emptySubst :: Subst
emptySubst = Subst IM.empty 0

-- | Construct a logic variable from a VarId.
logicVar :: VarId a -> Logic a
logicVar (VarId i) = Term.Var i

-- | Look up a binding for a variable ID.
lookupBinding :: Typeable a => Int -> Subst -> Maybe (Logic a)
lookupBinding i s =
  case IM.lookup i (substBindings s) of
    Nothing -> Nothing
    Just (SomeBinding term) -> cast term

-- | Dereference only the top-level variable (no deep traversal).
walkLogic :: (Repr a, Typeable a) => Subst -> Logic a -> Logic a
walkLogic s (Term.Var i) =
  case lookupBinding i s of
    Nothing -> Term.Var i
    Just term -> walkLogic s term
walkLogic _ t@(Term.Ground _) = t

-- | Apply substitution recursively through a logic term.
applySubstLogic :: (Repr a, Typeable a) => Subst -> Logic a -> Logic a
applySubstLogic s (Term.Var i) =
  case lookupBinding i s of
    Nothing -> Term.Var i
    Just term -> applySubstLogic s term
applySubstLogic s (Term.Ground r) =
  Term.Ground (Term.mapReified (applySubstLogic s) r)

-- | Occurs check to prevent cyclic bindings.
occurs :: (Repr a, Typeable a) => Int -> Logic a -> Subst -> Bool
occurs i t s =
  case walkLogic s t of
    Term.Var j -> i == j
    Term.Ground r ->
      any (\(Term.Field child) -> occurs i child s) (snd (Term.quote r))

-- | Extend the substitution with a new binding.
extendSubst :: (Repr a, Typeable a) => Int -> Logic a -> Subst -> Subst
extendSubst i term s =
  s { substBindings = IM.insert i (SomeBinding term) (substBindings s) }

-- | Unify two logic terms, producing an updated substitution.
unifyLogic :: (Repr a, Typeable a) => Logic a -> Logic a -> Subst -> Maybe Subst
unifyLogic t1 t2 s =
  case (walkLogic s t1, walkLogic s t2) of
    (Term.Var i, Term.Var j) | i == j -> Just s
    (Term.Var i, term) -> bindVar i term s
    (term, Term.Var i) -> bindVar i term s
    (Term.Ground r1, Term.Ground r2) -> unifyReified r1 r2 s
  where
    bindVar i term s'
      | occurs i term s' = Nothing
      | otherwise = Just (extendSubst i term s')

-- | Unify two reified values using structural decomposition.
unifyReified :: (Repr a, Typeable a) => Term.Reified a -> Term.Reified a -> Subst -> Maybe Subst
unifyReified r1 r2 s =
  case (Term.quote r1, Term.quote r2) of
    ((n1, fs1), (n2, fs2))
      | n1 /= n2 -> Nothing
      | length fs1 /= length fs2 -> Nothing
      | otherwise -> unifyFields fs1 fs2 s

-- | Unify paired field lists.
unifyFields :: [Term.Field] -> [Term.Field] -> Subst -> Maybe Subst
unifyFields [] [] s = Just s
unifyFields (Term.Field t1 : xs) (Term.Field t2 : ys) s =
  case cast t2 of
    Nothing -> Nothing
    Just t2' -> do
      s' <- unifyLogic t1 t2' s
      unifyFields xs ys s'
unifyFields _ _ _ = Nothing

-- | Execute a goal.
exec :: Goal -> Subst -> [Subst]
exec Success s      = [s]
exec Failure _      = []
exec (Conj g1 g2) s = concatMap (exec g2) (exec g1 s)
exec (Disj g1 g2) s = interleave (exec g1 s) (exec g2 s)
exec (Fresh f) s    =
  let v = VarId (substNextVar s)
      s' = s { substNextVar = substNextVar s + 1 }
  in exec (f v) s'
exec (Unify t1 t2) s =
  case unifyLogic t1 t2 s of
    Nothing -> []
    Just s' -> [s']
exec (Disunify t1 t2) s =
  case unifyLogic t1 t2 s of
    Nothing -> [s]
    Just _  -> []
exec (Neg g) s =
  case exec g s of
    [] -> [s]
    _  -> []

interleave :: [a] -> [a] -> [a]
interleave [] ys = ys
interleave (x:xs) ys = x : interleave ys xs
