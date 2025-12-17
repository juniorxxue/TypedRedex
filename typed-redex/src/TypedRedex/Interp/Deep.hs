{-# LANGUAGE TypeFamilies, GeneralisedNewtypeDeriving, DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FlexibleContexts #-}
{-# LANGUAGE GADTs, RankNTypes, TypeApplications, ScopedTypeVariables #-}

-- | DeepRedex: A deep embedding interpreter for TypedRedex
--
-- This interpreter builds a Goal AST instead of solving, which is useful
-- for rule extraction and analysis.
module TypedRedex.Interp.Deep
  ( DeepRedex
  , Goal(..)
  , runDeep
  , runDeepWith
  , prettyGoal
  , extractRule
  , extractAllRules
  , formatAsRule
  , formatAsRuleWithJudgment
  , deepVar  -- Helper to create logic variables for extraction
    -- * Pretty-printing extracted rules
  , printRules, printRules2, printRules3, printRules4, printRules5
    -- * Pretty-printing with custom formatters
  , printRulesWith, printRules2With, printRules3With, printRules4With, printRules5With
  ) where

import TypedRedex.Core.Internal.Redex
import TypedRedex.Core.Internal.Logic
import TypedRedex.DSL.Fresh (LTerm)
import TypedRedex.Interp.Format (formatCon, formatConWith, intercalate, TermFormatter(..), DefaultTermFormatter(..), JudgmentFormatter(..), defaultFormatJudgment)
import TypedRedex.Interp.PrettyPrint (VarNaming(..), namingByTag, subscriptNum)
import TypedRedex.DSL.Define (Applied(..), Applied2(..), Applied3(..), Applied4(..), Applied5(..))
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
  , dsFormatter  :: String -> [String] -> String  -- term formatter function
  }

initState :: DeepState
initState = initStateWith formatCon

initStateWith :: (String -> [String] -> String) -> DeepState
initStateWith fmt = DeepState 0 [] 0 fmt

-- Maximum depth for expanding calls (0 = just record calls, don't expand bodies)
-- Set to 2 for rule extraction: level 1 expands judgment to rules, level 2 expands rule bodies
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
freshName n = "e" ++ subscriptNum n

--------------------------------------------------------------------------------
-- Redex Instance
--------------------------------------------------------------------------------

instance Redex DeepRedex where
  newtype RVar DeepRedex t = DVar Int
    deriving (Functor)

  -- For rule extraction: reuse variables from ArgVar instead of creating new ones
  fresh_ FreshVar k = do
    n <- gets dsVarCounter
    modify $ \s -> s { dsVarCounter = n + 1 }
    k (DVar n)
  fresh_ (ArgVar (Free (DVar n))) k = k (DVar n)  -- Reuse existing variable
  fresh_ (ArgVar (Ground _)) k = do  -- Ground term: create fresh var (shouldn't happen often)
    n <- gets dsVarCounter
    modify $ \s -> s { dsVarCounter = n + 1 }
    k (DVar n)

  unify x y = do
    fmt <- gets dsFormatter
    recordGoal $ GUnify (prettyLFmt fmt x) (prettyLFmt fmt y)

  -- | No interleaving for rule extraction
  suspend = id

  -- | Capture relation calls for rule extraction
  call_ _ rel = do
    -- Record this call with its arguments (resolve CapturedTerms to strings)
    args <- mapM prettyCaptured (relTerms rel)
    recordGoal $ GCall (relName rel) args
    -- Optionally expand the body up to max depth
    depth <- gets dsDepth
    when (depth < maxDepth) $ do
      modify $ \s -> s { dsDepth = depth + 1 }
      relBody rel
      modify $ \s -> s { dsDepth = depth }

  displayVar (DVar n) = freshName n

-- | Pretty-print a CapturedTerm for DeepRedex (no substitution to apply)
prettyCaptured :: CapturedTerm DeepRedex -> DeepRedex String
prettyCaptured (CapturedTerm term) = do
  fmt <- gets dsFormatter
  pure $ prettyLFmt fmt term

instance EqVar DeepRedex where
  varEq (DVar a) (DVar b) = a == b

--------------------------------------------------------------------------------
-- Pretty-printing Logic terms (local version for DeepRedex)
--------------------------------------------------------------------------------

-- | Pretty-print a logic term. Outputs variable markers «TAG:ID» for later renumbering.
-- Uses default term formatting.
prettyL :: forall a. LogicType a => Logic a (RVar DeepRedex) -> String
prettyL = prettyLFmt formatCon

-- | Pretty-print a logic term with a formatter function.
prettyLFmt :: forall a. LogicType a => (String -> [String] -> String) -> Logic a (RVar DeepRedex) -> String
prettyLFmt _ (Free (DVar n)) = "«" ++ vnTag (varNaming @a) ++ ":" ++ show n ++ "»"
prettyLFmt fmt (Ground r) = prettyReifiedFmt fmt r

-- | Pretty-print a logic term with a custom term formatter (typeclass version).
prettyLWith :: forall a fmt. (LogicType a, TermFormatter fmt) => fmt -> Logic a (RVar DeepRedex) -> String
prettyLWith fmt = prettyLFmt (formatConWith fmt)

prettyReifiedFmt :: LogicType a => (String -> [String] -> String) -> Reified a (RVar DeepRedex) -> String
prettyReifiedFmt fmt r =
  let (con, fields) = quote r
  in fmt (name con) (map (prettyFieldFmt fmt) fields)

prettyFieldFmt :: (String -> [String] -> String) -> Field a (RVar DeepRedex) -> String
prettyFieldFmt fmt (Field _ logic) = prettyLogicAnyFmt fmt logic

-- | Pretty-print any logic term with variable markers for later renumbering.
prettyLogicAnyFmt :: forall t. LogicType t => (String -> [String] -> String) -> Logic t (RVar DeepRedex) -> String
prettyLogicAnyFmt _ (Free (DVar n)) = "«" ++ vnTag (varNaming @t) ++ ":" ++ show n ++ "»"
prettyLogicAnyFmt fmt (Ground r) = prettyReifiedFmt fmt r

-- Typeclass-based versions for backward compatibility
prettyReifiedWith :: (LogicType a, TermFormatter fmt) => fmt -> Reified a (RVar DeepRedex) -> String
prettyReifiedWith fmt = prettyReifiedFmt (formatConWith fmt)

prettyFieldWith :: TermFormatter fmt => fmt -> Field a (RVar DeepRedex) -> String
prettyFieldWith fmt = prettyFieldFmt (formatConWith fmt)

prettyLogicAnyWith :: forall t fmt. (LogicType t, TermFormatter fmt) => fmt -> Logic t (RVar DeepRedex) -> String
prettyLogicAnyWith fmt = prettyLogicAnyFmt (formatConWith fmt)

-- Keep old names for backward compatibility within this module
prettyReified :: LogicType a => Reified a (RVar DeepRedex) -> String
prettyReified = prettyReifiedFmt formatCon

prettyField :: Field a (RVar DeepRedex) -> String
prettyField = prettyFieldFmt formatCon

prettyLogicAny :: forall t. LogicType t => Logic t (RVar DeepRedex) -> String
prettyLogicAny = prettyLogicAnyFmt formatCon

--------------------------------------------------------------------------------
-- Running and extracting
--------------------------------------------------------------------------------

-- | Run a DeepRedex computation and extract the Goal AST
runDeep :: DeepRedex () -> Goal
runDeep = runDeepWith DefaultTermFormatter

-- | Run a DeepRedex computation with a custom formatter
runDeepWith :: TermFormatter fmt => fmt -> DeepRedex () -> Goal
runDeepWith fmt (DeepRedex m) =
  let finalState = execState m (initStateWith (formatConWith fmt))
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
-- Variable renumbering for readable rule output
--------------------------------------------------------------------------------

-- | Parse all variable markers «TAG:ID» from a string
parseVarMarkers :: String -> [(String, Int, String)]  -- (tag, id, full marker)
parseVarMarkers [] = []
parseVarMarkers ('«':rest) =
  case break (== ':') rest of
    (tag, ':':rest2) ->
      case break (== '»') rest2 of
        (idStr, '»':rest3) ->
          case reads idStr of
            [(n, "")] -> (tag, n, "«" ++ tag ++ ":" ++ idStr ++ "»") : parseVarMarkers rest3
            _ -> parseVarMarkers rest3
        _ -> parseVarMarkers rest2
    _ -> parseVarMarkers rest
parseVarMarkers (_:rest) = parseVarMarkers rest

-- | Build a renumbering map: (tag, oldId) -> newLocalId
buildRenumberMap :: [(String, Int, String)] -> [((String, Int), Int)]
buildRenumberMap markers =
  let -- Group by tag, preserving first-occurrence order
      grouped = groupByTag markers
      -- Assign local IDs within each group (0, 1, 2, ...)
      numbered = concatMap numberGroup grouped
  in numbered
  where
    groupByTag :: [(String, Int, String)] -> [(String, [Int])]
    groupByTag ms =
      let tags = nub [t | (t, _, _) <- ms]
          getIds t = nub [i | (t', i, _) <- ms, t == t']
      in [(t, getIds t) | t <- tags]

    numberGroup :: (String, [Int]) -> [((String, Int), Int)]
    numberGroup (tag, ids) = [((tag, oldId), newId) | (oldId, newId) <- zip ids [0..]]

    nub :: Eq a => [a] -> [a]
    nub [] = []
    nub (x:xs) = x : nub (filter (/= x) xs)

-- | Get variable name by tag and local index (delegates to PrettyPrint)
varNameByTag :: String -> Int -> String
varNameByTag tag = vnName (namingByTag tag)

-- | Renumber all variable markers in a string with local per-rule numbering
renumberVars :: String -> String
renumberVars s =
  let markers = parseVarMarkers s
      renumberMap = buildRenumberMap markers
      lookupNew tag oldId = case lookup (tag, oldId) renumberMap of
        Just newId -> varNameByTag tag newId
        Nothing -> "?" ++ tag ++ show oldId
  in substituteMarkers lookupNew s

substituteMarkers :: (String -> Int -> String) -> String -> String
substituteMarkers _ [] = []
substituteMarkers lookupNew ('«':rest) =
  case break (== ':') rest of
    (tag, ':':rest2) ->
      case break (== '»') rest2 of
        (idStr, '»':rest3) ->
          case reads idStr of
            [(n, "")] -> lookupNew tag n ++ substituteMarkers lookupNew rest3
            _ -> '«' : substituteMarkers lookupNew rest
        _ -> '«' : substituteMarkers lookupNew rest
    _ -> '«' : substituteMarkers lookupNew rest
substituteMarkers lookupNew (c:rest) = c : substituteMarkers lookupNew rest

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
-- Returns (rule_name, conclusion_patterns, premises)
-- where premises are (judgment_name, args) tuples for later formatting
extractRule :: Goal -> (String, [String], [(String, [String])])
extractRule goal =
  let (ruleName, unifs, prems) = collectParts 0 [] goal  -- 0=Initial, 1=InConclusion, 2=InPremises
      -- Extract the RHS of unifications (the actual patterns)
      patterns = map snd unifs
  in (ruleName, patterns, prems)
  where
    -- Phase: 0=Initial (looking for rule name), 1=InConclusion (collecting unifs), 2=InPremises
    collectParts :: Int -> [(String, String)] -> Goal -> (String, [(String, String)], [(String, [String])])
    collectParts _ unifs GTrue = ("", unifs, [])
    collectParts 1 unifs (GUnify l r) = ("", unifs ++ [(l, r)], [])  -- Collect unifications in conclusion phase
    collectParts _ unifs (GUnify _ _) = ("", unifs, [])  -- Skip other unifications
    collectParts 0 unifs (GCall name _) = (name, unifs, [])  -- First GCall is the rule name
    collectParts _ unifs (GCall name args) = ("", unifs, [(name, args)])  -- Premise as (name, args) tuple
    -- GConde after conclusion: this represents a judgment call (prem $ judgment args)
    -- Extract premise from first branch, using judgment name (not rule name)
    collectParts phase unifs (GConde branches) | phase >= 1 =
      case branches of
        (b:_) -> case extractPremiseFromBranch b of
                   Just prem -> ("", unifs, [prem])
                   Nothing -> ("", unifs, [])
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
    -- Returns (judgment_name, args) tuple where judgment_name is inferred from rule name
    extractPremiseFromBranch :: Goal -> Maybe (String, [String])
    extractPremiseFromBranch (GCall name args) =
      -- Infer judgment name from rule name (e.g., "typeof-lam" -> "typeof", "substTy" stays "substTy")
      let judgmentName = takeWhile (/= '-') name
      in Just (if null judgmentName then name else judgmentName, args)
    extractPremiseFromBranch (GSeq g _) = extractPremiseFromBranch g
    extractPremiseFromBranch (GConde (b:_)) = extractPremiseFromBranch b
    extractPremiseFromBranch _ = Nothing

-- | Format extracted rule as ASCII inference rule
-- Takes the judgment name (for formatting conclusion) and rule name (for labeling)
formatAsRule :: String -> Goal -> String
formatAsRule = formatAsRuleWith DefaultTermFormatter

-- | Format extracted rule with a custom formatter
formatAsRuleWith :: JudgmentFormatter fmt => fmt -> String -> Goal -> String
formatAsRuleWith fmt = formatAsRuleWithJudgmentWith fmt ""

-- | Format extracted rule with explicit judgment name for conclusion formatting
-- If judgment name is empty, falls back to rule name
-- Applies per-rule variable renumbering for readable output
formatAsRuleWithJudgment :: String -> String -> Goal -> String
formatAsRuleWithJudgment = formatAsRuleWithJudgmentWith DefaultTermFormatter

-- | Format extracted rule with custom formatter and explicit judgment name
formatAsRuleWithJudgmentWith :: JudgmentFormatter fmt => fmt -> String -> String -> Goal -> String
formatAsRuleWithJudgmentWith fmt judgmentName ruleName goal =
  let (_, patterns, premTuples) = extractRule goal
      -- Use judgment name if provided, otherwise use rule name for formatting
      jname = if null judgmentName then ruleName else judgmentName
      conclusion = formatJudgment fmt jname patterns
      -- Format premises using the formatter
      prems = map (\(pname, pargs) -> formatJudgment fmt pname pargs) premTuples
      maxLen = maximum $ length conclusion : map length prems
      line = replicate (maxLen + 4) '─'
      raw = (if null prems then "" else unlines (map ("  " ++) prems)) ++
            "  " ++ line ++ " [" ++ ruleName ++ "]\n" ++
            "  " ++ conclusion
  in renumberVars raw  -- Apply per-rule variable renumbering

--------------------------------------------------------------------------------
-- Helper for creating variables in extraction
--------------------------------------------------------------------------------

-- | Create a logic variable for use in rule extraction.
-- Use deepVar 0, deepVar 1, etc. for different variables.
deepVar :: Int -> Logic a (RVar DeepRedex)
deepVar n = Free (DVar n)

--------------------------------------------------------------------------------
-- Pretty-printing extracted rules
--------------------------------------------------------------------------------

-- | Print all rules for a unary relation.
printRules :: (LogicType a)
           => String
           -> (LTerm a DeepRedex -> Applied DeepRedex a)
           -> IO ()
printRules judgmentName rel = do
  let goal = runDeep $ app1Goal $ rel (deepVar 0)
  let rules = extractAllRules goal
  mapM_ (\(name, ruleGoal) -> do
    putStrLn $ formatAsRuleWithJudgment judgmentName name ruleGoal
    putStrLn "") rules

-- | Print all rules for a binary relation.
printRules2 :: (LogicType a, LogicType b)
            => String
            -> (LTerm a DeepRedex -> LTerm b DeepRedex -> Applied2 DeepRedex a b)
            -> IO ()
printRules2 judgmentName rel = do
  let goal = runDeep $ app2Goal $ rel (deepVar 0) (deepVar 1)
  let rules = extractAllRules goal
  mapM_ (\(name, ruleGoal) -> do
    putStrLn $ formatAsRuleWithJudgment judgmentName name ruleGoal
    putStrLn "") rules

-- | Print all rules for a ternary relation.
printRules3 :: (LogicType a, LogicType b, LogicType c)
            => String
            -> (LTerm a DeepRedex -> LTerm b DeepRedex -> LTerm c DeepRedex -> Applied3 DeepRedex a b c)
            -> IO ()
printRules3 judgmentName rel = do
  let goal = runDeep $ app3Goal $ rel (deepVar 0) (deepVar 1) (deepVar 2)
  let rules = extractAllRules goal
  mapM_ (\(name, ruleGoal) -> do
    putStrLn $ formatAsRuleWithJudgment judgmentName name ruleGoal
    putStrLn "") rules

-- | Print all rules for a quaternary relation.
printRules4 :: (LogicType a, LogicType b, LogicType c, LogicType d)
            => String
            -> (LTerm a DeepRedex -> LTerm b DeepRedex -> LTerm c DeepRedex -> LTerm d DeepRedex -> Applied4 DeepRedex a b c d)
            -> IO ()
printRules4 judgmentName rel = do
  let goal = runDeep $ app4Goal $ rel (deepVar 0) (deepVar 1) (deepVar 2) (deepVar 3)
  let rules = extractAllRules goal
  mapM_ (\(name, ruleGoal) -> do
    putStrLn $ formatAsRuleWithJudgment judgmentName name ruleGoal
    putStrLn "") rules

-- | Print all rules for a 5-ary relation.
printRules5 :: (LogicType a, LogicType b, LogicType c, LogicType d, LogicType e)
            => String
            -> (LTerm a DeepRedex -> LTerm b DeepRedex -> LTerm c DeepRedex -> LTerm d DeepRedex -> LTerm e DeepRedex -> Applied5 DeepRedex a b c d e)
            -> IO ()
printRules5 judgmentName rel = do
  let goal = runDeep $ app5Goal $ rel (deepVar 0) (deepVar 1) (deepVar 2) (deepVar 3) (deepVar 4)
  let rules = extractAllRules goal
  mapM_ (\(name, ruleGoal) -> do
    putStrLn $ formatAsRuleWithJudgment judgmentName name ruleGoal
    putStrLn "") rules

--------------------------------------------------------------------------------
-- Pretty-printing extracted rules with custom formatter
--------------------------------------------------------------------------------

-- | Print all rules for a unary relation with custom formatter.
printRulesWith :: (LogicType a, TermFormatter fmt, JudgmentFormatter fmt)
               => fmt
               -> String
               -> (LTerm a DeepRedex -> Applied DeepRedex a)
               -> IO ()
printRulesWith fmt judgmentName rel = do
  let goal = runDeepWith fmt $ app1Goal $ rel (deepVar 0)
  let rules = extractAllRules goal
  mapM_ (\(name, ruleGoal) -> do
    putStrLn $ formatAsRuleWithJudgmentWith fmt judgmentName name ruleGoal
    putStrLn "") rules

-- | Print all rules for a binary relation with custom formatter.
printRules2With :: (LogicType a, LogicType b, TermFormatter fmt, JudgmentFormatter fmt)
                => fmt
                -> String
                -> (LTerm a DeepRedex -> LTerm b DeepRedex -> Applied2 DeepRedex a b)
                -> IO ()
printRules2With fmt judgmentName rel = do
  let goal = runDeepWith fmt $ app2Goal $ rel (deepVar 0) (deepVar 1)
  let rules = extractAllRules goal
  mapM_ (\(name, ruleGoal) -> do
    putStrLn $ formatAsRuleWithJudgmentWith fmt judgmentName name ruleGoal
    putStrLn "") rules

-- | Print all rules for a ternary relation with custom formatter.
printRules3With :: (LogicType a, LogicType b, LogicType c, TermFormatter fmt, JudgmentFormatter fmt)
                => fmt
                -> String
                -> (LTerm a DeepRedex -> LTerm b DeepRedex -> LTerm c DeepRedex -> Applied3 DeepRedex a b c)
                -> IO ()
printRules3With fmt judgmentName rel = do
  let goal = runDeepWith fmt $ app3Goal $ rel (deepVar 0) (deepVar 1) (deepVar 2)
  let rules = extractAllRules goal
  mapM_ (\(name, ruleGoal) -> do
    putStrLn $ formatAsRuleWithJudgmentWith fmt judgmentName name ruleGoal
    putStrLn "") rules

-- | Print all rules for a quaternary relation with custom formatter.
printRules4With :: (LogicType a, LogicType b, LogicType c, LogicType d, TermFormatter fmt, JudgmentFormatter fmt)
                => fmt
                -> String
                -> (LTerm a DeepRedex -> LTerm b DeepRedex -> LTerm c DeepRedex -> LTerm d DeepRedex -> Applied4 DeepRedex a b c d)
                -> IO ()
printRules4With fmt judgmentName rel = do
  let goal = runDeepWith fmt $ app4Goal $ rel (deepVar 0) (deepVar 1) (deepVar 2) (deepVar 3)
  let rules = extractAllRules goal
  mapM_ (\(name, ruleGoal) -> do
    putStrLn $ formatAsRuleWithJudgmentWith fmt judgmentName name ruleGoal
    putStrLn "") rules

-- | Print all rules for a 5-ary relation with custom formatter.
printRules5With :: (LogicType a, LogicType b, LogicType c, LogicType d, LogicType e, TermFormatter fmt, JudgmentFormatter fmt)
                => fmt
                -> String
                -> (LTerm a DeepRedex -> LTerm b DeepRedex -> LTerm c DeepRedex -> LTerm d DeepRedex -> LTerm e DeepRedex -> Applied5 DeepRedex a b c d e)
                -> IO ()
printRules5With fmt judgmentName rel = do
  let goal = runDeepWith fmt $ app5Goal $ rel (deepVar 0) (deepVar 1) (deepVar 2) (deepVar 3) (deepVar 4)
  let rules = extractAllRules goal
  mapM_ (\(name, ruleGoal) -> do
    putStrLn $ formatAsRuleWithJudgmentWith fmt judgmentName name ruleGoal
    putStrLn "") rules
