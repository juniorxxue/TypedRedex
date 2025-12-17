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
  -- * Term formatting (shared by interpreters)
, formatCon
, subscriptNum
, intercalate
, neg  -- re-export from Redex
) where
import TypedRedex.Core.Internal.Redex
import TypedRedex.Core.Internal.Logic
import Control.Applicative (asum)
import Data.Maybe (fromMaybe)

type Var' a rel = Var a (RVar rel)
type L a rel = Logic a (RVar rel)

--------------------------------------------------------------------------------
-- Term Pretty-Printing (shared by DeepRedex and TracingRedex)
--------------------------------------------------------------------------------

-- | Format constructor application nicely.
--
-- This provides consistent rendering of terms across all interpreters:
-- - Lambda: @(λ:τ. e)@ or @(λ. e)@
-- - Application: @(e₁ e₂)@
-- - Types: @(τ₁ → τ₂)@, @(∀. τ)@
-- - Contexts: @Γ, x:τ@
formatCon :: String -> [String] -> String
-- Terms (System F has annotated lambda, PCF has unannotated)
formatCon "App" [f, a] = "(" ++ f ++ " " ++ a ++ ")"
formatCon "Lam" [ty, b] = "(λ:" ++ ty ++ ". " ++ b ++ ")"  -- System F: annotated lambda
formatCon "Lam" [b] = "(λ." ++ b ++ ")"                     -- PCF: unannotated lambda
formatCon "Var" [n] = case parseNat n of
    Just k  -> "x" ++ subscriptNum (show k)
    Nothing -> n
  where
    -- Parse a Nat-formatted string like "0", "S(0)", "S(S(0))" to Int
    parseNat :: String -> Maybe Int
    parseNat "0" = Just 0
    parseNat ('S':'(':rest) = case parseNat (init rest) of  -- init removes trailing ')'
      Just k -> Just (k + 1)
      Nothing -> Nothing
    parseNat s | all isDigit s = Just (read s)
    parseNat _ = Nothing
    isDigit c = c `elem` "0123456789"
formatCon "Zero" [] = "0"
formatCon "Succ" [e] = "S(" ++ e ++ ")"
formatCon "Pred" [e] = "pred(" ++ e ++ ")"
formatCon "Ifz" [c, t, f] = "ifz(" ++ c ++ ", " ++ t ++ ", " ++ f ++ ")"
formatCon "Fix" [e] = "fix(" ++ e ++ ")"
-- Natural numbers
formatCon "Z" [] = "0"
formatCon "S" [n] = "S(" ++ n ++ ")"
-- System F Types
formatCon "TUnit" [] = "Unit"
formatCon "TVar" [n] = "α" ++ subscriptNum n
formatCon "TArr" [a, b] = "(" ++ a ++ " → " ++ b ++ ")"
formatCon "TAll" [ty] = "(∀. " ++ ty ++ ")"
-- System F Terms
formatCon "Unit" [] = "()"
formatCon "TLam" [b] = "(Λ." ++ b ++ ")"
formatCon "TApp" [e, ty] = "(" ++ e ++ " [" ++ ty ++ "])"
-- STLC Bidir Types
formatCon "→" [a, b] = "(" ++ a ++ " → " ++ b ++ ")"
-- Contexts
formatCon "Nil" [] = "·"
formatCon "·" [] = "·"
formatCon "TmBind" [ty, ctx] = ctx ++ ", x:" ++ ty
formatCon "TyBind" [ctx] = ctx ++ ", α"
formatCon "Cons" [ty, ctx] = ctx ++ ", " ++ ty
formatCon "," [ty, ctx] = ctx ++ ", " ++ ty
-- Default
formatCon n [] = n
formatCon n args = n ++ "(" ++ intercalate ", " args ++ ")"

-- | Convert a number string to subscript
subscriptNum :: String -> String
subscriptNum = concatMap toSub
  where
    toSub '0' = "₀"; toSub '1' = "₁"; toSub '2' = "₂"; toSub '3' = "₃"
    toSub '4' = "₄"; toSub '5' = "₅"; toSub '6' = "₆"; toSub '7' = "₇"
    toSub '8' = "₈"; toSub '9' = "₉"; toSub c = [c]

intercalate :: String -> [String] -> String
intercalate _ [] = ""
intercalate _ [x] = x
intercalate sep (x:xs) = x ++ sep ++ intercalate sep xs

--------------------------------------------------------------------------------
-- Pretty-printing Logic terms
--------------------------------------------------------------------------------

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
relation n f a_ = Relation n [CapturedTerm a_] $ argument a_ f

relation2 :: (Redex rel, LogicType a, LogicType b) => String -> (L a rel -> L b rel -> rel ()) -> L a rel -> L b rel -> Relation rel
relation2 n f a_ b_ = Relation n [CapturedTerm a_, CapturedTerm b_] $ argument2 a_ b_ f

relation3 :: (Redex rel, LogicType a, LogicType b, LogicType c) => String -> (L a rel -> L b rel -> L c rel -> rel ()) -> L a rel -> L b rel -> L c rel -> Relation rel
relation3 n f a_ b_ c_ = Relation n [CapturedTerm a_, CapturedTerm b_, CapturedTerm c_] $ argument3 a_ b_ c_ f

relation4 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d) => String -> (L a rel -> L b rel -> L c rel -> L d rel -> rel ()) -> L a rel -> L b rel -> L c rel -> L d rel -> Relation rel
relation4 n f a_ b_ c_ d_ = Relation n [CapturedTerm a_, CapturedTerm b_, CapturedTerm c_, CapturedTerm d_] $ argument4 a_ b_ c_ d_ f

relation5 :: (Redex rel, LogicType a, LogicType b, LogicType c, LogicType d, LogicType e) => String -> (L a rel -> L b rel -> L c rel -> L d rel -> L e rel -> rel ()) -> L a rel -> L b rel -> L c rel -> L d rel -> L e rel -> Relation rel
relation5 n f a_ b_ c_ d_ e_ = Relation n [CapturedTerm a_, CapturedTerm b_, CapturedTerm c_, CapturedTerm d_, CapturedTerm e_] $ argument5 a_ b_ c_ d_ e_ f

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
