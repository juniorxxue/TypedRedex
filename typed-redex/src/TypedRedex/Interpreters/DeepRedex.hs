{-# LANGUAGE TypeFamilies, GeneralisedNewtypeDeriving, DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FlexibleContexts #-}
{-# LANGUAGE GADTs, RankNTypes #-}
module TypedRedex.Interpreters.DeepRedex
  ( DeepRedex
  , Goal(..)
  , runDeep
  , prettyGoal
  , extractRule
  , extractAllRules
  , formatAsRule
  , formatAsRuleWithJudgment
  , deepVar  -- Helper to create logic variables for extraction
  ) where

import TypedRedex.Core.Internal.Redex
import TypedRedex.Core.Internal.Logic
import Control.Applicative
import Control.Monad (when)
import Control.Monad.State

--------------------------------------------------------------------------------
-- Deep Embedding AST
--
-- This captures the structure of a Redex relation as data.
--------------------------------------------------------------------------------

data Goal
  = GUnify String String          -- x <=> y (or x = pattern)
  | GFresh String Goal            -- fresh x. goal
  | GConde [Goal]                 -- conde [g1, g2, ...]
  | GCall String [String]         -- call relation(arg1, arg2, ...)
  | GSeq Goal Goal                -- g1 >> g2
  | GTrue                         -- success
  deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Deep Redex Interpreter State
--------------------------------------------------------------------------------

data DeepState = DeepState
  { dsVarCounter :: Int
  , dsGoals      :: [Goal]  -- accumulated goals (in reverse order)
  , dsDepth      :: Int     -- recursion depth for limiting expansion
  }

initState :: DeepState
initState = DeepState 0 [] 0

-- Maximum depth for expanding calls (0 = just record calls, don't expand bodies)
-- Set to 1 for rule extraction with premises visible
maxDepth :: Int
maxDepth = 1

--------------------------------------------------------------------------------
-- Deep Redex Interpreter
--
-- Builds a Goal AST instead of solving.
--------------------------------------------------------------------------------

newtype DeepRedex a = DeepRedex (State DeepState a)
  deriving (Functor, Applicative, Monad, MonadState DeepState)

instance Alternative DeepRedex where
  empty = DeepRedex $ pure (error "DeepRedex: empty")
  a <|> b = do
    -- Capture both branches as Conde
    s0 <- get
    let savedGoals = dsGoals s0
    -- Run branch a
    put $ s0 { dsGoals = [] }
    resultA <- a
    goalsA <- gets (reverse . dsGoals)
    -- Run branch b
    put $ s0 { dsGoals = [] }
    _ <- b
    goalsB <- gets (reverse . dsGoals)
    -- Combine as Conde
    put $ s0 { dsGoals = GConde [seqGoals goalsA, seqGoals goalsB] : savedGoals }
    return resultA

-- | Sequence a list of goals
seqGoals :: [Goal] -> Goal
seqGoals [] = GTrue
seqGoals [g] = g
seqGoals (g:gs) = GSeq g (seqGoals gs)

-- | Record a goal
recordGoal :: Goal -> DeepRedex ()
recordGoal g = modify $ \s -> s { dsGoals = g : dsGoals s }

-- | Generate fresh variable name using subscript indices
freshName :: Int -> String
freshName n = "e" ++ subscript n
  where
    subscript i = map toSubscript (show i)
    toSubscript '0' = '₀'
    toSubscript '1' = '₁'
    toSubscript '2' = '₂'
    toSubscript '3' = '₃'
    toSubscript '4' = '₄'
    toSubscript '5' = '₅'
    toSubscript '6' = '₆'
    toSubscript '7' = '₇'
    toSubscript '8' = '₈'
    toSubscript '9' = '₉'
    toSubscript c   = c

--------------------------------------------------------------------------------
-- Redex Instance
--------------------------------------------------------------------------------

instance Redex DeepRedex where
  newtype RVar DeepRedex t = DVar Int
    deriving (Functor)

  fresh_ _ k = do
    n <- gets dsVarCounter
    modify $ \s -> s { dsVarCounter = n + 1 }
    k (DVar n)

  unify x y = do
    recordGoal $ GUnify (prettyL x) (prettyL y)

  -- | No interleaving for rule extraction
  suspend = id

  -- | Capture relation calls for rule extraction
  call_ _ rel = do
    -- Record this call with its arguments
    recordGoal $ GCall (relName rel) (relArgs rel)
    -- Optionally expand the body up to max depth
    depth <- gets dsDepth
    when (depth < maxDepth) $ do
      modify $ \s -> s { dsDepth = depth + 1 }
      relBody rel
      modify $ \s -> s { dsDepth = depth }

  displayVar (DVar n) = freshName n

instance EqVar DeepRedex where
  varEq (DVar a) (DVar b) = a == b

--------------------------------------------------------------------------------
-- Pretty-printing Logic terms (local version for DeepRedex)
--------------------------------------------------------------------------------

prettyL :: LogicType a => Logic a (RVar DeepRedex) -> String
prettyL (Free (DVar n)) = freshName n
prettyL (Ground r) = prettyReified r

prettyReified :: LogicType a => Reified a (RVar DeepRedex) -> String
prettyReified r =
  let (con, fields) = quote r
  in formatCon (name con) (map prettyField fields)

prettyField :: Field a (RVar DeepRedex) -> String
prettyField (Field _ logic) = prettyLogicAny logic

prettyLogicAny :: LogicType t => Logic t (RVar DeepRedex) -> String
prettyLogicAny (Free (DVar n)) = freshName n
prettyLogicAny (Ground r) = prettyReified r

-- | Format constructor application nicely (customizable per type)
formatCon :: String -> [String] -> String
-- Terms (System F has annotated lambda, PCF has unannotated)
formatCon "App" [f, a] = "(" ++ f ++ " " ++ a ++ ")"
formatCon "Lam" [ty, b] = "(λ:" ++ ty ++ ". " ++ b ++ ")"  -- System F: annotated lambda
formatCon "Lam" [b] = "(λ." ++ b ++ ")"                     -- PCF: unannotated lambda
formatCon "Var" [n] = if all isSubscriptOrDigit n then "x" ++ subscriptNum n else n
  where isSubscriptOrDigit c = c `elem` "0123456789₀₁₂₃₄₅₆₇₈₉"
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
-- Running and extracting
--------------------------------------------------------------------------------

-- | Run a DeepRedex computation and extract the Goal AST
runDeep :: DeepRedex () -> Goal
runDeep (DeepRedex m) =
  let finalState = execState m initState
  in seqGoals (reverse $ dsGoals finalState)

--------------------------------------------------------------------------------
-- Pretty-printing Goals
--------------------------------------------------------------------------------

-- | Pretty-print a Goal as a string
prettyGoal :: Goal -> String
prettyGoal GTrue = "⊤"
prettyGoal (GUnify l r) = l ++ " = " ++ r
prettyGoal (GFresh x g) = "∃" ++ x ++ ". " ++ prettyGoal g
prettyGoal (GConde gs) = "(" ++ intercalate " ∣ " (map prettyGoal gs) ++ ")"
prettyGoal (GCall name args) =
  if null args
  then name
  else name ++ "(" ++ intercalate ", " args ++ ")"
prettyGoal (GSeq g1 g2) = prettyGoal g1 ++ ", " ++ prettyGoal g2

--------------------------------------------------------------------------------
-- Extract and format as inference rule
--------------------------------------------------------------------------------

-- | Extract all sub-rules from a combined relation (like rules2/rules3)
-- Returns a list of (rule-name, goal) pairs
extractAllRules :: Goal -> [(String, Goal)]
extractAllRules goal = case findConde goal of
  Just branches -> map extractRuleName (flattenConde branches)
  Nothing -> [extractRuleName goal]  -- Single rule
  where
    -- Find the GConde in a goal
    findConde :: Goal -> Maybe [Goal]
    findConde (GConde gs) = Just gs
    findConde (GSeq _ g2) = findConde g2
    findConde _ = Nothing

    -- Flatten nested GConde from asum/foldr
    flattenConde :: [Goal] -> [Goal]
    flattenConde [] = []
    flattenConde (g:gs) = case g of
      GConde nested -> flattenConde nested ++ flattenConde gs
      GTrue -> flattenConde gs  -- Skip empty branches
      _ -> g : flattenConde gs

    -- Extract rule name from the first GCall in a branch
    extractRuleName :: Goal -> (String, Goal)
    extractRuleName g = case findFirstCall g of
      Just name -> (name, g)
      Nothing -> ("?", g)

    findFirstCall :: Goal -> Maybe String
    findFirstCall (GCall name _) = Just name
    findFirstCall (GSeq g1 _) = findFirstCall g1
    findFirstCall _ = Nothing

-- | Extract premises and conclusion from a Goal
-- Returns (judgment_name, conclusion_patterns, premises)
-- The conclusion patterns come from GUnify statements that bind the relation arguments
extractRule :: Goal -> (String, [String], [String])
extractRule goal =
  let (ruleName, unifs, prems) = collectParts 0 [] goal  -- 0=Initial, 1=InConclusion, 2=InPremises
      -- Extract the RHS of unifications (the actual patterns)
      patterns = map snd unifs
  in (ruleName, patterns, prems)
  where
    -- Phase: 0=Initial (looking for rule name), 1=InConclusion (collecting unifs), 2=InPremises
    collectParts :: Int -> [(String, String)] -> Goal -> (String, [(String, String)], [String])
    collectParts _ unifs GTrue = ("", unifs, [])
    collectParts 1 unifs (GUnify l r) = ("", unifs ++ [(l, r)], [])  -- Collect unifications in conclusion phase
    collectParts _ unifs (GUnify _ _) = ("", unifs, [])  -- Skip other unifications
    collectParts 0 unifs (GCall name _) = (name, unifs, [])  -- First GCall is the rule name
    collectParts _ unifs (GCall name args) = ("", unifs, [formatCall name args])  -- Premise as direct call
    -- GConde after conclusion (phases 1 or 2): extract premise from first branch
    collectParts phase unifs (GConde branches) | phase >= 1 =
      case branches of
        (b:_) -> let prem = extractPremiseFromBranch b
                 in ("", unifs, if null prem then [] else [prem])
        _ -> ("", unifs, [])
    collectParts _ unifs (GConde _) = ("", unifs, [])  -- Skip GConde in phase 0
    collectParts phase unifs (GSeq g1 g2) =
      let (r1, u1, p1) = collectParts phase unifs g1
          -- Compute next phase based on what we found in g1
          foundRuleName = not (null r1)
          foundPremise = not (null p1)
          nextPhase = case phase of
            0 -> if foundRuleName then 1 else 0
            1 -> if foundPremise then 2 else 1
            _ -> 2
          (r2, u2, p2) = collectParts nextPhase u1 g2
          rname = if null r1 then r2 else r1
      in (rname, u2, p1 ++ p2)
    collectParts phase unifs (GFresh _ g) = collectParts phase unifs g

    -- Extract premise from a GConde branch (which is typically a GCall for a specific rule)
    extractPremiseFromBranch :: Goal -> String
    extractPremiseFromBranch (GCall name args) =
      -- Try to infer judgment name from rule name (e.g., "value-lam" -> "value")
      let judgmentName = takeWhile (/= '-') name
      in if null judgmentName || judgmentName == name
         then formatCall name args  -- No "-" found, use full name
         else formatCall judgmentName args
    extractPremiseFromBranch (GSeq g _) = extractPremiseFromBranch g
    extractPremiseFromBranch (GConde (b:_)) = extractPremiseFromBranch b
    extractPremiseFromBranch _ = ""

    formatCall :: String -> [String] -> String
    -- Typing judgments
    formatCall "typeof" [ctx, e, ty] = ctx ++ " ⊢ " ++ e ++ " : " ++ ty
    formatCall "synth" [ctx, e, ty] = ctx ++ " ⊢ " ++ e ++ " ⇒ " ++ ty
    formatCall "check" [ctx, e, ty] = ctx ++ " ⊢ " ++ e ++ " ⇐ " ++ ty
    -- Context lookup
    formatCall "lookup" [ctx, n, ty] = ctx ++ "(" ++ n ++ ") = " ++ ty
    formatCall "lookupTm" [ctx, n, ty] = ctx ++ "(" ++ n ++ ") = " ++ ty
    -- Step relation (both judgment name and common rule names)
    formatCall "step" [a, b] = a ++ " ⟶ " ++ b
    formatCall "β" [a, b] = a ++ " ⟶ " ++ b
    formatCall "app" [a, b] = a ++ " ⟶ " ++ b
    -- Value predicate
    formatCall "value" [a] = "value(" ++ a ++ ")"
    -- Substitution
    formatCall "subst0" [body, arg, result] = "[" ++ arg ++ "/0]" ++ body ++ " = " ++ result
    formatCall "subst" [depth, subTy, ty, result] = "[" ++ subTy ++ "/" ++ depth ++ "]" ++ ty ++ " = " ++ result
    formatCall "substTy" [depth, subTy, ty, result] = "[" ++ subTy ++ "/" ++ depth ++ "]" ++ ty ++ " = " ++ result
    formatCall "substTyVar" [depth, subTy, n, result] = "[" ++ subTy ++ "/" ++ depth ++ "](TVar " ++ n ++ ") = " ++ result
    -- Shifting
    formatCall "shiftTy" [cutoff, amount, ty, result] = "↑" ++ superscript cutoff ++ "·" ++ superscript amount ++ " " ++ ty ++ " = " ++ result
    formatCall "shiftTyVar" [cutoff, amount, n, result] = "↑" ++ superscript cutoff ++ "·" ++ superscript amount ++ " (TVar " ++ n ++ ") = " ++ result
    -- Arithmetic on naturals
    formatCall "natEq" [n, m] = n ++ " = " ++ m
    formatCall "natLt" [n, m] = n ++ " < " ++ m
    formatCall "addNat" [n, m, s] = n ++ " + " ++ m ++ " = " ++ s
    -- Default: function-style
    formatCall n args = n ++ "(" ++ intercalate ", " args ++ ")"

    superscript :: String -> String
    superscript = map toSuper
      where
        toSuper '0' = '⁰'; toSuper '1' = '¹'; toSuper '2' = '²'; toSuper '3' = '³'
        toSuper '4' = '⁴'; toSuper '5' = '⁵'; toSuper '6' = '⁶'; toSuper '7' = '⁷'
        toSuper '8' = '⁸'; toSuper '9' = '⁹'; toSuper c = c

-- | Format a conclusion based on judgment name and arguments
formatConclusion :: String -> [String] -> String
-- Typing judgments
formatConclusion "typeof" [ctx, e, ty] = ctx ++ " ⊢ " ++ e ++ " : " ++ ty
formatConclusion "synth" [ctx, e, ty] = ctx ++ " ⊢ " ++ e ++ " ⇒ " ++ ty
formatConclusion "check" [ctx, e, ty] = ctx ++ " ⊢ " ++ e ++ " ⇐ " ++ ty
-- Context lookup
formatConclusion "lookup" [ctx, n, ty] = ctx ++ "(" ++ n ++ ") = " ++ ty
formatConclusion "lookupTm" [ctx, n, ty] = ctx ++ "(" ++ n ++ ") = " ++ ty
-- Step relation
formatConclusion "step" [a, b] = a ++ " ⟶ " ++ b
-- Value predicate
formatConclusion "value" [a] = "value(" ++ a ++ ")"
-- Substitution
formatConclusion "subst0" [body, arg, result] = "[" ++ arg ++ "/0]" ++ body ++ " = " ++ result
formatConclusion "substTy" [depth, subTy, ty, result] = "[" ++ subTy ++ "/" ++ depth ++ "]" ++ ty ++ " = " ++ result
formatConclusion "substTyVar" [depth, subTy, n, result] = "[" ++ subTy ++ "/" ++ depth ++ "](TVar " ++ n ++ ") = " ++ result
-- Shifting
formatConclusion "shiftTy" [cutoff, amount, ty, result] = "↑" ++ toSuper cutoff ++ "·" ++ toSuper amount ++ " " ++ ty ++ " = " ++ result
  where toSuper = map (\c -> case c of '0'->'⁰';'1'->'¹';'2'->'²';'3'->'³';'4'->'⁴';'5'->'⁵';'6'->'⁶';'7'->'⁷';'8'->'⁸';'9'->'⁹';x->x)
formatConclusion "shiftTyVar" [cutoff, amount, n, result] = "↑" ++ toSuper cutoff ++ "·" ++ toSuper amount ++ " (TVar " ++ n ++ ") = " ++ result
  where toSuper = map (\c -> case c of '0'->'⁰';'1'->'¹';'2'->'²';'3'->'³';'4'->'⁴';'5'->'⁵';'6'->'⁶';'7'->'⁷';'8'->'⁸';'9'->'⁹';x->x)
-- Arithmetic on naturals
formatConclusion "natEq" [n, m] = n ++ " = " ++ m
formatConclusion "natLt" [n, m] = n ++ " < " ++ m
formatConclusion "addNat" [n, m, s] = n ++ " + " ++ m ++ " = " ++ s
-- Default: function-style
formatConclusion name args = name ++ "(" ++ intercalate ", " args ++ ")"

-- | Format extracted rule as ASCII inference rule
-- Takes the judgment name (for formatting conclusion) and rule name (for labeling)
formatAsRule :: String -> Goal -> String
formatAsRule = formatAsRuleWithJudgment ""

-- | Format extracted rule with explicit judgment name for conclusion formatting
-- If judgment name is empty, falls back to rule name
formatAsRuleWithJudgment :: String -> String -> Goal -> String
formatAsRuleWithJudgment judgmentName ruleName goal =
  let (_, patterns, prems) = extractRule goal
      -- Use judgment name if provided, otherwise use rule name for formatting
      jname = if null judgmentName then ruleName else judgmentName
      -- Renumber variables to start from 1
      allVars = collectVars (prems ++ patterns)
      renumberMap = zip allVars [1..]
      -- Two-pass renumbering to avoid chain replacement:
      -- First pass: rename to temporary names (e₂ -> __tmp_2__)
      -- Second pass: rename temps to final names (__tmp_2__ -> e₁)
      toTemp old = "__tmp_" ++ show old ++ "__"
      pass1 s = foldr (\(old, _) acc -> replace (freshName old) (toTemp old) acc) s renumberMap
      pass2 s = foldr (\(old, new) acc -> replace (toTemp old) (freshName new) acc) s renumberMap
      renumber = pass2 . pass1
      prems' = map renumber prems
      patterns' = map renumber patterns
      conclusion = formatConclusion jname patterns'
      maxLen = maximum $ length conclusion : map length prems'
      line = replicate (maxLen + 4) '─'
  in (if null prems' then "" else unlines (map ("  " ++) prems')) ++
     "  " ++ line ++ " [" ++ ruleName ++ "]\n" ++
     "  " ++ conclusion

-- | Collect all variable indices from strings
collectVars :: [String] -> [Int]
collectVars strs = unique $ concatMap findVars strs
  where
    findVars :: String -> [Int]
    findVars [] = []
    findVars ('e':rest) = case parseSubscript rest of
      Just (n, rest') -> n : findVars rest'
      Nothing -> findVars rest
    findVars (_:rest) = findVars rest

    parseSubscript :: String -> Maybe (Int, String)
    parseSubscript s =
      let (digits, rest) = span isSubscript s
      in if null digits then Nothing else Just (subscriptToInt digits, rest)

    isSubscript c = c `elem` "₀₁₂₃₄₅₆₇₈₉"

    subscriptToInt :: String -> Int
    subscriptToInt = read . map fromSubscript
      where
        fromSubscript '₀' = '0'
        fromSubscript '₁' = '1'
        fromSubscript '₂' = '2'
        fromSubscript '₃' = '3'
        fromSubscript '₄' = '4'
        fromSubscript '₅' = '5'
        fromSubscript '₆' = '6'
        fromSubscript '₇' = '7'
        fromSubscript '₈' = '8'
        fromSubscript '₉' = '9'
        fromSubscript c   = c

    unique :: [Int] -> [Int]
    unique [] = []
    unique (x:xs) = x : unique (filter (/= x) xs)

-- | Replace all occurrences of a substring
replace :: String -> String -> String -> String
replace _ _ [] = []
replace old new s@(c:cs)
  | old `isPrefixOf` s = new ++ replace old new (drop (length old) s)
  | otherwise = c : replace old new cs

isPrefixOf :: String -> String -> Bool
isPrefixOf [] _ = True
isPrefixOf _ [] = False
isPrefixOf (x:xs) (y:ys) = x == y && isPrefixOf xs ys

--------------------------------------------------------------------------------
-- Helper for creating variables in extraction
--------------------------------------------------------------------------------

-- | Create a logic variable for use in rule extraction.
-- Use deepVar 0, deepVar 1, etc. for different variables.
deepVar :: Int -> Logic a (RVar DeepRedex)
deepVar n = Free (DVar n)
