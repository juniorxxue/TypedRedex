{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

-- | Alpha-equivalent binders.
module TypedRedex.Nominal.Bind
  ( Bind(..)
  , bind
  , unbind
  ) where

import Data.Typeable (Typeable)

import TypedRedex.Core.Term
import TypedRedex.Nominal (NominalAtom(..), Permute(..), Hash(..))
import TypedRedex.Pretty (Pretty(..), Doc(..), (<+>), prettyLogic)

-- | A binder that binds a name in a body.
data Bind name body = Bind !name body
  deriving (Eq, Show)

-- | Smart constructor for binder terms.
bind :: (NominalAtom name, Repr name, Repr body, Typeable name, Typeable body)
     => Term name
     -> Term body
     -> Term (Bind name body)
bind (Term varsN n) (Term varsB b) =
  Term (varsN <> varsB) (Ground (BindR n b))

-- | Extract binder pieces when the term is ground.
unbind :: Logic (Bind name body) -> Maybe (Logic name, Logic body)
unbind (Ground (BindR n b)) = Just (n, b)
unbind _ = Nothing

instance {-# OVERLAPPING #-} (NominalAtom name, Permute name body) => Permute name (Bind name body) where
  swap a b (Bind n body) = Bind (swapAtom a b n) (swap a b body)

instance {-# OVERLAPPABLE #-} (Permute name body) => Permute name (Bind other body) where
  swap a b (Bind n body) = Bind n (swap a b body)

instance (NominalAtom name, Repr name, Repr body, Typeable name, Typeable body, Permute name body, Hash name body)
    => Repr (Bind name body) where
  data Reified (Bind name body) = BindR (Logic name) (Logic body)

  project (Bind n b) = BindR (Ground (project n)) (Ground (project b))

  reify (BindR (Ground rn) (Ground rb)) = Bind <$> reify rn <*> reify rb
  reify _ = Nothing

  quote (BindR n b) = ("Bind", [Field n, Field b])

  mapReified f (BindR n b) = BindR (f n) (f b)

  unifyReified unif addHash (BindR n1 b1) (BindR n2 b2) s =
    case (n1, n2) of
      (Ground rn1, Ground rn2) ->
        case (reify rn1, reify rn2) of
          (Just a, Just b)
            | a == b -> unif b1 b2 s
            | otherwise ->
                case (b1, b2) of
                  (_, Ground rb2) ->
                    case reify rb2 of
                      Just body2 -> do
                        s' <- addHash (Ground rn1) b2 s
                        let swapped = swap a b body2
                        unif b1 (Ground (project swapped)) s'
                      Nothing -> do
                        s' <- addHash (Ground rn1) b2 s
                        unif b1 b2 s'
                  (Ground rb1, _) ->
                    case reify rb1 of
                      Just body1 -> do
                        s' <- addHash (Ground rn2) b1 s
                        let swapped = swap b a body1
                        unif (Ground (project swapped)) b2 s'
                      Nothing -> do
                        s' <- addHash (Ground rn2) b1 s
                        unif b1 b2 s'
                  _ -> do
                    s' <- addHash (Ground rn1) b2 s
                    unif b1 b2 s'
          _ -> unif n1 n2 s >>= \s' -> unif b1 b2 s'
      _ -> unif n1 n2 s >>= \s' -> unif b1 b2 s'

instance (NominalAtom name, Permute name body, Hash name body, Pretty name, Pretty body) => Pretty (Bind name body) where
  prettyReified (BindR n b) = do
    dn <- prettyLogic n
    db <- prettyLogic b
    pure (dn <+> Doc "." <+> db)
