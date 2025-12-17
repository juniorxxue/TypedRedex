-- | Term formatting utilities.
--
-- This module provides pretty-printing utilities for logic terms,
-- including constructor formatting and term-to-string conversion.
module TypedRedex.Interp.Format
  ( -- * Constructor formatting
    formatCon
    -- * Logic term pretty-printing
  , prettyLogic
    -- * String utilities
  , intercalate
    -- * Re-exports from PrettyPrint
  , subscriptNum
  ) where

import TypedRedex.Core.Internal.Redex
import TypedRedex.Core.Internal.Logic
import TypedRedex.Interp.PrettyPrint (subscriptStr)

-- | Re-export subscriptStr as subscriptNum for backward compatibility.
subscriptNum :: String -> String
subscriptNum = subscriptStr

--------------------------------------------------------------------------------
-- Constructor formatting
--------------------------------------------------------------------------------

-- | Format constructor application nicely.
--
-- This provides consistent rendering of terms across all interpreters:
--
-- * Lambda: @(λ:τ. e)@ or @(λ. e)@
-- * Application: @(e₁ e₂)@
-- * Types: @(τ₁ → τ₂)@, @(∀. τ)@
-- * Contexts: @Γ, x:τ@
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

--------------------------------------------------------------------------------
-- Logic term pretty-printing
--------------------------------------------------------------------------------

-- | Pretty-print a logic value using quote and displayVar.
-- Used by tracing interpreters to capture relation arguments.
prettyLogic :: (Redex rel, LogicType a) => Logic a (RVar rel) -> String
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

--------------------------------------------------------------------------------
-- String utilities
--------------------------------------------------------------------------------

-- | Intercalate a separator between list elements.
intercalate :: String -> [String] -> String
intercalate _ [] = ""
intercalate _ [x] = x
intercalate sep (x:xs) = x ++ sep ++ intercalate sep xs
