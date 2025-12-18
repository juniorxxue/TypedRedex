{-# LANGUAGE TypeFamilies, GeneralisedNewtypeDeriving, DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FlexibleContexts #-}
{-# LANGUAGE GADTs, RankNTypes, TypeApplications, ScopedTypeVariables #-}
{-# LANGUAGE DataKinds, TypeOperators, AllowAmbiguousTypes #-}

-- | DeepRedex: Rule extraction interpreter for TypedRedex
--
-- Directly builds inference rules from relation definitions.
-- No intermediate AST - the structure IS the extraction.
module TypedRedex.Interp.Deep
  ( -- * Core types
    DeepRedex
  , ExtractedRule(..)
    -- * Running the interpreter
  , runDeep
  , runDeepWith
    -- * Formatting
  , formatRule
  , formatRuleWith
  , deepVar
    -- * Pretty-printing extracted rules (generic for any arity)
  , printRules
  , printRulesWith
  , ApplyDeepVars(..)
  ) where

import TypedRedex.Core.Internal.Redex
import TypedRedex.Core.Internal.Logic
import TypedRedex.DSL.Fresh (LTerm)
import TypedRedex.Interp.Format (formatCon, formatConWith, intercalate, TermFormatter(..), DefaultTermFormatter(..), JudgmentFormatter(..))
import TypedRedex.Interp.PrettyPrint (VarNaming(..), LogicVarNaming(..), namingByTag, subscriptNum)
import TypedRedex.DSL.Define (Applied(..), CurriedR)
import Control.Applicative
import Control.Monad (when)
import Control.Monad.State
import Data.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- Extracted Rule (the only data structure we need)
--------------------------------------------------------------------------------

-- | An inference rule with name, conclusion patterns, and premises.
data ExtractedRule = ExtractedRule
  { erName     :: String                  -- ^ Rule name (e.g., "typeof-lam")
  , erPatterns :: [String]                -- ^ Conclusion patterns
  , erPremises :: [(String, [String])]    -- ^ Premises as (judgment-name, args)
  } deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Rule Builder (state during tracing)
--------------------------------------------------------------------------------

-- | State for building a single rule
data RuleBuilder = RuleBuilder
  { rbName        :: String
  , rbInConclusion :: Bool                -- ^ After markConclusion?
  , rbPatterns    :: [String]             -- ^ Conclusion patterns (reverse order)
  , rbPremises    :: [(String, [String])] -- ^ Premises (reverse order)
  } deriving (Show)

emptyBuilder :: RuleBuilder
emptyBuilder = RuleBuilder "" False [] []

finishRule :: RuleBuilder -> ExtractedRule
finishRule rb = ExtractedRule
  { erName = rbName rb
  , erPatterns = reverse (rbPatterns rb)
  , erPremises = reverse (rbPremises rb)
  }

--------------------------------------------------------------------------------
-- Deep Interpreter State
--------------------------------------------------------------------------------

data DeepState = DeepState
  { dsVarCounter :: Int
  , dsBuilder    :: RuleBuilder           -- ^ Current rule being built
  , dsRules      :: [ExtractedRule]       -- ^ Completed rules
  , dsDepth      :: Int                   -- ^ Expansion depth
  , dsFormatter  :: String -> [String] -> String
  }

initState :: DeepState
initState = initStateWith formatCon

initStateWith :: (String -> [String] -> String) -> DeepState
initStateWith fmt = DeepState 0 emptyBuilder [] 0 fmt

--------------------------------------------------------------------------------
-- Deep Redex Interpreter
--------------------------------------------------------------------------------

newtype DeepRedex a = DeepRedex (State DeepState a)
  deriving (Functor, Applicative, Monad, MonadState DeepState)

instance Alternative DeepRedex where
  empty = DeepRedex $ pure (error "DeepRedex: empty")
  a <|> b = do
    s0 <- get
    -- Run branch a
    put $ s0 { dsBuilder = emptyBuilder, dsRules = [] }
    _ <- a
    rulesA <- gets dsRules
    builderA <- gets dsBuilder
    let rulesA' = if null (rbName builderA) then rulesA else finishRule builderA : rulesA
    -- Run branch b
    put $ s0 { dsBuilder = emptyBuilder, dsRules = [] }
    _ <- b
    rulesB <- gets dsRules
    builderB <- gets dsBuilder
    let rulesB' = if null (rbName builderB) then rulesB else finishRule builderB : rulesB
    -- Combine rules
    put $ s0 { dsRules = dsRules s0 ++ reverse rulesA' ++ reverse rulesB' }
    pure (error "DeepRedex: <|> result")

--------------------------------------------------------------------------------
-- Redex Instance
--------------------------------------------------------------------------------

instance Redex DeepRedex where
  newtype RVar DeepRedex t = DVar Int
    deriving (Functor)

  fresh_ FreshVar k = do
    n <- gets dsVarCounter
    modify $ \s -> s { dsVarCounter = n + 1 }
    k (DVar n)
  fresh_ (ArgVar (Free (DVar n))) k = k (DVar n)
  fresh_ (ArgVar (Ground _)) k = do
    n <- gets dsVarCounter
    modify $ \s -> s { dsVarCounter = n + 1 }
    k (DVar n)

  unify x y = do
    inConcl <- gets (rbInConclusion . dsBuilder)
    when inConcl $ do
      fmt <- gets dsFormatter
      let rhs = prettyLFmt fmt y
      modify $ \s -> s { dsBuilder = (dsBuilder s) { rbPatterns = rhs : rbPatterns (dsBuilder s) } }

  suspend = id

  call_ _ rel = do
    depth <- gets dsDepth
    if depth == 0
      then do
        -- Depth 0→1: This is a rule call, set the rule name
        modify $ \s -> s { dsBuilder = (dsBuilder s) { rbName = relName rel }, dsDepth = 1 }
        relBody rel
        modify $ \s -> s { dsDepth = 0 }
      else
        -- Depth > 0: Inside rule body, don't expand further
        pure ()

  displayVar (DVar n) = "e" ++ subscriptNum n

  markConclusion = modify $ \s ->
    s { dsBuilder = (dsBuilder s) { rbInConclusion = True } }

  markPremise name args = do
    argStrs <- mapM prettyCaptured args
    modify $ \s -> s { dsBuilder = (dsBuilder s) {
      rbPremises = (name, argStrs) : rbPremises (dsBuilder s)
    } }

prettyCaptured :: CapturedTerm DeepRedex -> DeepRedex String
prettyCaptured (CapturedTerm term) = do
  fmt <- gets dsFormatter
  pure $ prettyLFmt fmt term

instance EqVar DeepRedex where
  varEq (DVar a) (DVar b) = a == b

--------------------------------------------------------------------------------
-- Pretty-printing Logic terms
--------------------------------------------------------------------------------

prettyLFmt :: forall a. LogicType a => (String -> [String] -> String) -> Logic a (RVar DeepRedex) -> String
prettyLFmt _ (Free (DVar n)) = "«" ++ vnTag (varNaming @a) ++ ":" ++ show n ++ "»"
prettyLFmt fmt (Ground r) = prettyReifiedFmt fmt r

prettyReifiedFmt :: LogicType a => (String -> [String] -> String) -> Reified a (RVar DeepRedex) -> String
prettyReifiedFmt fmt r =
  let (con, fields) = quote r
  in fmt (name con) (map (prettyFieldFmt fmt) fields)

prettyFieldFmt :: (String -> [String] -> String) -> Field a (RVar DeepRedex) -> String
prettyFieldFmt fmt (Field _ logic) = prettyLogicAnyFmt fmt logic

prettyLogicAnyFmt :: forall t. LogicType t => (String -> [String] -> String) -> Logic t (RVar DeepRedex) -> String
prettyLogicAnyFmt _ (Free (DVar n)) = "«" ++ vnTag (varNaming @t) ++ ":" ++ show n ++ "»"
prettyLogicAnyFmt fmt (Ground r) = prettyReifiedFmt fmt r

--------------------------------------------------------------------------------
-- Running and extracting
--------------------------------------------------------------------------------

-- | Run a DeepRedex computation and extract all rules
runDeep :: DeepRedex () -> [ExtractedRule]
runDeep = runDeepWith DefaultTermFormatter

-- | Run with a custom formatter
runDeepWith :: TermFormatter fmt => fmt -> DeepRedex () -> [ExtractedRule]
runDeepWith fmt (DeepRedex m) =
  let finalState = execState m (initStateWith (formatConWith fmt))
      builder = dsBuilder finalState
      rules = dsRules finalState
  in if null (rbName builder)
     then reverse rules
     else reverse (finishRule builder : rules)

--------------------------------------------------------------------------------
-- Variable renumbering
--------------------------------------------------------------------------------

-- | Remove duplicates preserving first-occurrence order
nub :: Eq a => [a] -> [a]
nub [] = []
nub (x:xs) = x : nub (filter (/= x) xs)

parseVarMarkers :: String -> [(String, Int)]
parseVarMarkers [] = []
parseVarMarkers ('«':rest) =
  case break (== ':') rest of
    (tag, ':':rest2) ->
      case break (== '»') rest2 of
        (idStr, '»':rest3) ->
          case reads idStr of
            [(n, "")] -> (tag, n) : parseVarMarkers rest3
            _ -> parseVarMarkers rest3
        _ -> parseVarMarkers rest2
    _ -> parseVarMarkers rest
parseVarMarkers (_:rest) = parseVarMarkers rest

buildRenumberMap :: [(String, Int)] -> [((String, Int), Int)]
buildRenumberMap markers =
  let tags = nub [t | (t, _) <- markers]
      grouped = [(t, nub [i | (t', i) <- markers, t == t']) | t <- tags]
  in concatMap (\(tag, ids) -> [((tag, oldId), newId) | (oldId, newId) <- zip ids [0..]]) grouped

varNameByTag :: String -> Int -> String
varNameByTag tag = vnName (namingByTag tag)

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
-- Formatting rules
--------------------------------------------------------------------------------

-- | Format an extracted rule as ASCII inference rule
formatRule :: JudgmentFormatter fmt => fmt -> String -> ExtractedRule -> String
formatRule fmt judgmentName rule =
  let conclusion = formatJudgment fmt judgmentName (erPatterns rule)
      prems = map (\(pname, pargs) -> formatJudgment fmt pname pargs) (erPremises rule)
      maxLen = maximum $ length conclusion : map length prems
      line = replicate (maxLen + 4) '─'
      raw = (if null prems then "" else unlines (map ("  " ++) prems)) ++
            "  " ++ line ++ " [" ++ erName rule ++ "]\n" ++
            "  " ++ conclusion
  in renumberVars raw

-- | Format with default formatter
formatRuleWith :: String -> ExtractedRule -> String
formatRuleWith = formatRule DefaultTermFormatter

--------------------------------------------------------------------------------
-- Helper for creating variables
--------------------------------------------------------------------------------

-- | Create a logic variable for rule extraction
deepVar :: Int -> Logic a (RVar DeepRedex)
deepVar n = Free (DVar n)

--------------------------------------------------------------------------------
-- Applying deepVar to curried functions
--------------------------------------------------------------------------------

-- | Type class for applying deepVar with incrementing indices to curried functions.
-- This allows a single generic printRules to work for any arity.
class ApplyDeepVars ts where
  applyDeepVarsTo :: Proxy ts -> Int -> CurriedR DeepRedex ts result -> result

instance ApplyDeepVars '[] where
  applyDeepVarsTo _ _ r = r

instance (LogicType t, ApplyDeepVars ts) => ApplyDeepVars (t ': ts) where
  applyDeepVarsTo _ n f = applyDeepVarsTo (Proxy @ts) (n + 1) (f (deepVar n))

--------------------------------------------------------------------------------
-- Pretty-printing extracted rules (generic)
--------------------------------------------------------------------------------

-- | Print extracted rules for a judgment of any arity.
-- Uses type application to specify the type list, e.g.:
--
-- @
-- printRules \@'[Tm, Tm] \"step\" step
-- printRules \@'[Ctx, Tm, Ty] \"typeof\" typeof
-- @
printRules :: forall ts. ApplyDeepVars ts
           => String
           -> CurriedR DeepRedex ts (Applied DeepRedex ts)
           -> IO ()
printRules judgmentName rel = do
  let applied :: Applied DeepRedex ts
      applied = applyDeepVarsTo (Proxy @ts) 0 rel
  let rules = runDeep $ appGoal applied
  mapM_ (\r -> putStrLn (formatRuleWith judgmentName r) >> putStrLn "") rules

-- | Print extracted rules with a custom formatter.
printRulesWith :: forall ts fmt. (ApplyDeepVars ts, TermFormatter fmt, JudgmentFormatter fmt)
               => fmt
               -> String
               -> CurriedR DeepRedex ts (Applied DeepRedex ts)
               -> IO ()
printRulesWith fmt judgmentName rel = do
  let applied :: Applied DeepRedex ts
      applied = applyDeepVarsTo (Proxy @ts) 0 rel
  let rules = runDeepWith fmt $ appGoal applied
  mapM_ (\r -> putStrLn (formatRule fmt judgmentName r) >> putStrLn "") rules
