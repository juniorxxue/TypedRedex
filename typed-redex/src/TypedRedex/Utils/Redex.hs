{-# LANGUAGE Rank2Types, ApplicativeDo #-}
module TypedRedex.Utils.Redex
(
  flatteningUnify, evalFromRead
, fresh, fresh2, fresh3, fresh4, fresh5
, argument, argument2, argument3, argument4, argument5
, relation, relation2, relation3, relation4, relation5
, call, premise, embed
, eval
, run, run2, run3, run4, run5
, (===), (<=>)
, conde
, Var', L
, occursCheck
, prettyLogic
, neg  -- re-export from Redex
) where
import TypedRedex.Core.Internal.Redex
import TypedRedex.Core.Internal.Logic
import Control.Applicative (asum)
import Data.Maybe (fromMaybe)

type Var' a rel = Var a (RVar rel)
type L a rel = Logic a (RVar rel)

-- | Pretty-print a logic value using quote and displayVar.
-- Used by tracing interpreters to capture relation arguments.
prettyLogic :: (Redex rel, LogicType a) => L a rel -> String
prettyLogic (Free v) = displayVar v
prettyLogic (Ground r) = prettyReified r
  where
    prettyReified :: (Redex rel, LogicType a) => Reified a (RVar rel) -> String
    prettyReified r' =
      let (con, fields) = quote r'
      in formatCon (name con) (map prettyField fields)

    prettyField :: Redex rel => Field a (RVar rel) -> String
    prettyField (Field _ logic) = prettyLogicAny logic

    prettyLogicAny :: (Redex rel, LogicType t) => Logic t (RVar rel) -> String
    prettyLogicAny (Free v) = displayVar v
    prettyLogicAny (Ground r') = prettyReified r'

    formatCon :: String -> [String] -> String
    formatCon n [] = n
    formatCon n args = n ++ "(" ++ intercalate ", " args ++ ")"

    intercalate :: String -> [String] -> String
    intercalate _ [] = ""
    intercalate _ [x] = x
    intercalate sep (x:xs) = x ++ sep ++ intercalate sep xs

flatteningUnify :: (Alternative rel, LogicType a) => (forall a'. (LogicType a') => Var' a' rel -> L a' rel -> rel ()) -> L a rel -> L a rel -> rel ()
flatteningUnify unifyVar (Free a) b = unifyVar a b
flatteningUnify unifyVar a (Free b) = unifyVar b a
flatteningUnify unifyVar (Ground a) (Ground b) = unifyVal (flatteningUnify unifyVar) a b

evalFromRead :: (Redex rel, LogicType a) => (forall a'. (LogicType a') => Var' a' rel -> rel (Maybe a')) -> L a rel -> rel a
evalFromRead readVar (Ground x) = derefVal (evalFromRead readVar) x
evalFromRead readVar (Free v) = do
    x <- readVar v
    pure $ fromMaybe (error $ "Unbound variable: " ++ displayVar v) x

fresh :: (Redex rel, LogicType a) => (L a rel -> rel s) -> rel s
fresh f = fresh_ FreshVar $ f . Free

fresh2 :: (Redex rel, LogicType a, LogicType b) => (L a rel -> L b rel -> rel s) -> rel s
fresh2 f = fresh $ \a -> fresh $ \b -> f a b

fresh3 :: (Redex rel, LogicType a, LogicType b, LogicType c) => (L a rel -> L b rel -> L c rel -> rel s) -> rel s
fresh3 f = fresh $ \a -> fresh $ \b -> fresh $ \c -> f a b c

fresh4 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d) => (L a rel -> L b rel -> L c rel -> L d rel -> rel s) -> rel s
fresh4 f = fresh $ \a -> fresh $ \b -> fresh $ \c -> fresh $ \d -> f a b c d

fresh5 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d, LogicType e) => (L a rel -> L b rel -> L c rel -> L d rel -> L e rel -> rel s) -> rel s
fresh5 f = fresh $ \a -> fresh $ \b -> fresh $ \c -> fresh $ \d -> fresh $ \e -> f a b c d e

argument :: (Redex rel, LogicType a) => L a rel -> (L a rel -> rel s) -> rel s
argument x f = fresh_ (ArgVar x) $ f . Free

argument2 :: (Redex rel, LogicType a, LogicType b) => L a rel -> L b rel -> (L a rel -> L b rel -> rel s) -> rel s
argument2 a_ b_ f = argument a_ $ \a -> argument b_ $ \b -> f a b

argument3 :: (Redex rel, LogicType a, LogicType b, LogicType c) => L a rel -> L b rel -> L c rel -> (L a rel -> L b rel -> L c rel -> rel s) -> rel s
argument3 a_ b_ c_ f = argument a_ $ \a -> argument b_ $ \b -> argument c_ $ \c -> f a b c

argument4 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d) => L a rel -> L b rel -> L c rel -> L d rel -> (L a rel -> L b rel -> L c rel -> L d rel -> rel s) -> rel s
argument4 a_ b_ c_ d_ f = argument a_ $ \a -> argument b_ $ \b -> argument c_ $ \c -> argument d_ $ \d -> f a b c d

argument5 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d, LogicType e) => L a rel -> L b rel -> L c rel -> L d rel -> L e rel -> (L a rel -> L b rel -> L c rel -> L d rel -> L e rel -> rel s) -> rel s
argument5 a_ b_ c_ d_ e_ f = argument a_ $ \a -> argument b_ $ \b -> argument c_ $ \c -> argument d_ $ \d -> argument e_ $ \e -> f a b c d e

relation :: (Redex rel, LogicType a) => String -> (L a rel -> rel ()) -> L a rel -> Relation rel
relation n f a_ = Relation n [prettyLogic a_] $ argument a_ f

relation2 :: (Redex rel, LogicType a, LogicType b) => String -> (L a rel -> L b rel -> rel ()) -> L a rel -> L b rel -> Relation rel
relation2 n f a_ b_ = Relation n [prettyLogic a_, prettyLogic b_] $ argument2 a_ b_ f

relation3 :: (Redex rel, LogicType a, LogicType b, LogicType c) => String -> (L a rel -> L b rel -> L c rel -> rel ()) -> L a rel -> L b rel -> L c rel -> Relation rel
relation3 n f a_ b_ c_ = Relation n [prettyLogic a_, prettyLogic b_, prettyLogic c_] $ argument3 a_ b_ c_ f

relation4 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d) => String -> (L a rel -> L b rel -> L c rel -> L d rel -> rel ()) -> L a rel -> L b rel -> L c rel -> L d rel -> Relation rel
relation4 n f a_ b_ c_ d_ = Relation n [prettyLogic a_, prettyLogic b_, prettyLogic c_, prettyLogic d_] $ argument4 a_ b_ c_ d_ f

relation5 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d, LogicType e) => String -> (L a rel -> L b rel -> L c rel -> L d rel -> L e rel -> rel ()) -> L a rel -> L b rel -> L c rel -> L d rel -> L e rel -> Relation rel
relation5 n f a_ b_ c_ d_ e_ = Relation n [prettyLogic a_, prettyLogic b_, prettyLogic c_, prettyLogic d_, prettyLogic e_] $ argument5 a_ b_ c_ d_ e_ f

call :: (Redex rel) => Relation rel -> rel ()
call = call_ Opaque

premise :: (Redex rel) => Relation rel -> rel ()
premise = call

embed :: (Redex rel) => Relation rel -> rel ()
embed = call_ Transparent

eval :: (RedexEval rel, LogicType a) => L a rel -> rel a
eval (Free v) = derefVar v
eval (Ground x) = derefVal eval x

run :: (RedexEval rel, LogicType a) => (L a rel -> Relation rel) -> rel a
run f = fresh $ \x -> do
    _ <- embed $ f x
    x' <- eval x
    return x'

run2 :: (RedexEval rel, LogicType a, LogicType b) => (L a rel -> L b rel -> Relation rel) -> rel (a, b)
run2 f = fresh2 $ \x y -> do
    _ <- embed $ f x y
    a <- eval x
    b <- eval y
    return (a, b)

run3 :: (RedexEval rel, LogicType a, LogicType b, LogicType c) => (L a rel -> L b rel -> L c rel -> Relation rel) -> rel (a, b, c)
run3 f = fresh3 $ \x y z -> do
    _ <- embed $ f x y z
    a <- eval x
    b <- eval y
    c <- eval z
    return (a, b, c)

run4 :: (RedexEval rel, LogicType a, LogicType b, LogicType c, LogicType d) => (L a rel -> L b rel -> L c rel -> L d rel -> Relation rel) -> rel (a, b, c, d)
run4 f = fresh4 $ \x y z w -> do
    _ <- embed $ f x y z w
    a <- eval x
    b <- eval y
    c <- eval z
    d <- eval w
    return (a, b, c, d)

run5 :: (RedexEval rel, LogicType a, LogicType b, LogicType c, LogicType d, LogicType e) => (L a rel -> L b rel -> L c rel -> L d rel -> L e rel -> Relation rel) -> rel (a, b, c, d, e)
run5 f = fresh5 $ \x y z w q -> do
    _ <- embed $ f x y z w q
    a <- eval x
    b <- eval y
    c <- eval z
    d <- eval w
    e <- eval q
    return (a, b, c, d, e)


(===) :: (LogicType a, Redex rel) => L a rel -> Reified a (RVar rel) -> rel ()
a === b = unify a (Ground b)

(<=>) :: (LogicType a, Redex rel) => L a rel -> L a rel -> rel ()
a <=> b = unify a b

conde :: (Redex rel) => [rel a] -> rel a
conde = asum

occursCheck :: (LogicType b, EqVar rel) => Var' a rel -> L b rel -> Bool
occursCheck x (Free y) = x `varEq` y
occursCheck x (Ground y) = let (_, ys) = quote y in any (\(Field _ y') -> occursCheck x y') ys
