{-# LANGUAGE ScopedTypeVariables #-}

-- | Core term representation for logic programming
--
-- Pure symbolic terms without interpreter dependencies.
module TypedRedex.Core.Term
  ( -- * Terms
    Term(..)
  , Logic(..)
  , Field(..)
  -- * Repr class
  , Repr(..)
  -- * Smart constructors
  , ground
  , var
  , lift1
  , lift2
  , lift3
  -- * Display helpers
  , displayLogic
  , displayField
  ) where

import Data.Kind (Type)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Typeable (Typeable, cast)
import TypedRedex.Nominal (NominalAtom, Hash)
-- | A term with runtime variable tracking.
--
-- @a@ is the Haskell type this term represents.
data Term (a :: Type) = Term
  { termVars :: Set Int    -- ^ Runtime variable IDs (for mode checking)
  , termVal  :: Logic a    -- ^ The symbolic value
  }

-- | A logic value: either a variable or a ground constructor
data Logic a where
  Var    :: Int -> Logic a           -- ^ Unbound variable (by ID)
  Ground :: Reified a -> Logic a     -- ^ Constructor with children

-- | Existential wrapper for heterogeneous children
data Field where
  Field :: (Repr a, Typeable a) => Logic a -> Field

-- | Types that can participate in logic programming
--
-- Users define:
--   1. @data instance Reified MyType = ...@ with Logic children
--   2. @project@ to embed ground values
--   3. @reify@ to extract ground values (fails if vars remain)
--   4. @quote@ for pretty-printing and traversal
class Typeable a => Repr a where
  data Reified a :: Type

  -- | Embed a ground Haskell value
  project :: a -> Reified a

  -- | Extract ground value (Nothing if contains variables)
  reify :: Reified a -> Maybe a

  -- | Quote for display: constructor name and children
  quote :: Reified a -> (String, [Field])

  -- | Map over logic children inside a reified value.
  --
  -- Needed for applying substitutions during evaluation.
  mapReified :: (forall t. (Repr t, Typeable t) => Logic t -> Logic t)
             -> Reified a
             -> Reified a

  -- | Unify two reified values using a caller-supplied unifier for logic terms.
  --
  -- Override this to implement custom unification (e.g., alpha-equivalence).
  unifyReified
    :: (forall t. (Repr t, Typeable t) => Logic t -> Logic t -> s -> Maybe s)
    -> (forall name term.
           (NominalAtom name, Hash name term, Repr name, Repr term, Typeable name, Typeable term)
        => Logic name -> Logic term -> s -> Maybe s)
    -> Reified a
    -> Reified a
    -> s
    -> Maybe s
  unifyReified unif _addHash r1 r2 s =
    case (quote r1, quote r2) of
      ((n1, fs1), (n2, fs2))
        | n1 /= n2 -> Nothing
        | length fs1 /= length fs2 -> Nothing
        | otherwise -> unifyFields fs1 fs2 s
    where
      unifyFields [] [] s' = Just s'
      unifyFields (Field t1 : xs) (Field t2 : ys) s' =
        case cast t2 of
          Nothing -> Nothing
          Just t2' -> do
            s'' <- unif t1 t2' s'
            unifyFields xs ys s''
      unifyFields _ _ _ = Nothing

--------------------------------------------------------------------------------
-- Smart constructors
--------------------------------------------------------------------------------

-- | Embed a ground Haskell value as a Term
ground :: Repr a => a -> Term a
ground x = Term S.empty (Ground (project x))

-- | Create a variable term (used internally by fresh)
var :: Int -> Term a
var i = Term (S.singleton i) (Var i)

-- | Lift a unary constructor
lift1 :: (Logic a -> Logic b) -> Term a -> Term b
lift1 f (Term vars val) = Term vars (f val)

-- | Lift a binary constructor
lift2 :: (Logic a -> Logic b -> Logic c) -> Term a -> Term b -> Term c
lift2 f (Term v1 a) (Term v2 b) = Term (S.union v1 v2) (f a b)

-- | Lift a ternary constructor
lift3 :: (Logic a -> Logic b -> Logic c -> Logic d)
      -> Term a -> Term b -> Term c -> Term d
lift3 f (Term v1 a) (Term v2 b) (Term v3 c) = Term (S.unions [v1, v2, v3]) (f a b c)

--------------------------------------------------------------------------------
-- Display
--------------------------------------------------------------------------------

-- | Display a logic term
displayLogic :: Repr a => Logic a -> String
displayLogic (Var i)    = "?" ++ show i
displayLogic (Ground r) = case quote r of
  (name, [])     -> name
  (name, fields) -> name ++ "(" ++ commas (map displayField fields) ++ ")"
  where commas = foldr1 (\x y -> x ++ ", " ++ y)

-- | Display a field
displayField :: Field -> String
displayField (Field t) = displayLogic t
