{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ApplicativeDo #-}

module Shallow.Utils.Kanren
  ( fresh, fresh2, fresh3, fresh4, fresh5
  , (===), (<=>)
  , conde
  , call, embed
  , eval
  , run, run2
  , relation, relation2, relation3
  , L, Var'
  ) where

import Shallow.Core.Internal.Kanren
import Shallow.Core.Internal.Logic
import Control.Applicative (asum)

type Var' a rel = KVar rel (Logic a (KVar rel))
type L a rel = Logic a (KVar rel)

-- ============================================================================
-- Fresh variable generation
-- ============================================================================

fresh :: (Kanren rel, LogicType a) => (L a rel -> rel s) -> rel s
fresh f = fresh_ FreshVar $ f . Free

fresh2 :: (Kanren rel, LogicType a, LogicType b) =>
  (L a rel -> L b rel -> rel s) -> rel s
fresh2 f = fresh $ \a -> fresh $ \b -> f a b

fresh3 :: (Kanren rel, LogicType a, LogicType b, LogicType c) =>
  (L a rel -> L b rel -> L c rel -> rel s) -> rel s
fresh3 f = fresh $ \a -> fresh $ \b -> fresh $ \c -> f a b c

fresh4 :: (Kanren rel, LogicType a, LogicType b, LogicType c, LogicType d) =>
  (L a rel -> L b rel -> L c rel -> L d rel -> rel s) -> rel s
fresh4 f = fresh $ \a -> fresh $ \b -> fresh $ \c -> fresh $ \d -> f a b c d

fresh5 :: (Kanren rel, LogicType a, LogicType b, LogicType c, LogicType d, LogicType e) =>
  (L a rel -> L b rel -> L c rel -> L d rel -> L e rel -> rel s) -> rel s
fresh5 f = fresh $ \a -> fresh $ \b -> fresh $ \c -> fresh $ \d -> fresh $ \e -> f a b c d e

-- ============================================================================
-- Unification
-- ============================================================================

(===) :: (LogicType a, Kanren rel) => L a rel -> L a rel -> rel ()
a === b = unify a b

(<=>) :: (LogicType a, Kanren rel) => L a rel -> L a rel -> rel ()
a <=> b = unify a b

-- ============================================================================
-- Relations
-- ============================================================================

relation :: (Kanren rel, LogicType a) =>
  String -> (L a rel -> rel ()) -> L a rel -> Relation rel
relation n f a_ = Relation n $ do
  fresh_ (ArgVar a_) $ \var -> f (Free var)

relation2 :: (Kanren rel, LogicType a, LogicType b) =>
  String -> (L a rel -> L b rel -> rel ()) -> L a rel -> L b rel -> Relation rel
relation2 n f a_ b_ = Relation n $ do
  fresh_ (ArgVar a_) $ \varA ->
    fresh_ (ArgVar b_) $ \varB ->
      f (Free varA) (Free varB)

relation3 :: (Kanren rel, LogicType a, LogicType b, LogicType c) =>
  String -> (L a rel -> L b rel -> L c rel -> rel ()) ->
  L a rel -> L b rel -> L c rel -> Relation rel
relation3 n f a_ b_ c_ = Relation n $ do
  fresh_ (ArgVar a_) $ \varA ->
    fresh_ (ArgVar b_) $ \varB ->
      fresh_ (ArgVar c_) $ \varC ->
        f (Free varA) (Free varB) (Free varC)

-- ============================================================================
-- Calling relations
-- ============================================================================

call :: (Kanren rel) => Relation rel -> rel ()
call = call_ Opaque

embed :: (Kanren rel) => Relation rel -> rel ()
embed = call_ Transparent

-- ============================================================================
-- Conde (disjunction)
-- ============================================================================

conde :: (Kanren rel) => [rel a] -> rel a
conde = asum

-- ============================================================================
-- Evaluation
-- ============================================================================

eval :: (KanrenEval rel, LogicType a) => L a rel -> rel a
eval (Free v) = derefVar v
eval (Ground x) = derefVal eval x

-- ============================================================================
-- Running queries
-- ============================================================================

run :: (KanrenEval rel, LogicType a) => (L a rel -> Relation rel) -> rel a
run f = fresh $ \x -> do
  _ <- embed $ f x
  x' <- eval x
  return x'

run2 :: (KanrenEval rel, LogicType a, LogicType b) =>
  (L a rel -> L b rel -> Relation rel) -> rel (a, b)
run2 f = fresh2 $ \x y -> do
  _ <- embed $ f x y
  a <- eval x
  b <- eval y
  return (a, b)
