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

-- Maximum depth for expanding calls (0 = expand top level only, 1 = one level of calls, 2 = two levels)
maxDepth :: Int
maxDepth = 2

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
formatCon "App" [f, a] = "(" ++ f ++ " " ++ a ++ ")"
formatCon "Lam" [b] = "(λ." ++ b ++ ")"
formatCon "Var" [n] = "var(" ++ n ++ ")"
formatCon "Zero" [] = "0"
formatCon "Succ" [e] = "succ(" ++ e ++ ")"
formatCon "Pred" [e] = "pred(" ++ e ++ ")"
formatCon "Ifz" [c, t, f] = "ifz(" ++ c ++ ", " ++ t ++ ", " ++ f ++ ")"
formatCon "Fix" [e] = "fix(" ++ e ++ ")"
formatCon "Z" [] = "0"
formatCon "S" [n] = "S(" ++ n ++ ")"
formatCon n [] = n
formatCon n args = n ++ "(" ++ intercalate ", " args ++ ")"

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
-- Returns (premises, conclusion_lhs, conclusion_rhs)
-- For a binary relation like step, the first two unifications set up:
--   input_var = input_pattern   (LHS of conclusion = input_pattern)
--   output_var = output_pattern (RHS of conclusion = output_pattern)
extractRule :: Goal -> ([String], String, String)
extractRule goal =
  let (prems, concls) = collectParts True goal  -- True = skip first GCall (relation name)
  in case concls of
       [] -> (prems, "?", "?")
       [(_, r)] -> (prems, r, "?")  -- Only one unify, use its RHS as LHS
       ((_, lhs):(_, rhs):_) -> (prems, lhs, rhs)  -- First two unifications give patterns
  where
    collectParts :: Bool -> Goal -> ([String], [(String, String)])
    collectParts _ GTrue = ([], [])
    collectParts _ (GUnify l r) = ([], [(l, r)])
    collectParts skipFirst (GCall name args)
      | skipFirst = ([], [])  -- Skip the first GCall (the relation name)
      | otherwise = ([formatCall name args], [])
    collectParts skipFirst (GSeq g1 g2) =
      let (p1, c1) = collectParts skipFirst g1
          -- After first element, don't skip anymore
          (p2, c2) = collectParts False g2
      in (p1 ++ p2, c1 ++ c2)
    collectParts _ (GConde _) = ([], [])  -- conde is top-level, not a premise
    collectParts skipFirst (GFresh _ g) = collectParts skipFirst g

    formatCall :: String -> [String] -> String
    formatCall "step" [a, b] = a ++ " ⟶ " ++ b
    formatCall "value" [a] = "value(" ++ a ++ ")"
    formatCall "subst0" [body, arg, result] = "[" ++ arg ++ "/0]" ++ body ++ " = " ++ result
    formatCall n args = n ++ "(" ++ intercalate ", " args ++ ")"

-- | Format extracted rule as ASCII inference rule
formatAsRule :: String -> Goal -> String
formatAsRule ruleName goal =
  let (prems, lhs, rhs) = extractRule goal
      -- Renumber variables to start from 1
      allVars = collectVars (prems ++ [lhs, rhs])
      renumberMap = zip allVars [1..]
      renumber s = foldr (\(old, new) acc -> replace (freshName old) (freshName new) acc) s renumberMap
      prems' = map renumber prems
      lhs' = renumber lhs
      rhs' = renumber rhs
      conclusion = lhs' ++ " ⟶ " ++ rhs'
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
