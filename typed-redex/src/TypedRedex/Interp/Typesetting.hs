{-# LANGUAGE TypeFamilies, GeneralisedNewtypeDeriving, DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FlexibleContexts #-}
{-# LANGUAGE GADTs, RankNTypes, TypeApplications, ScopedTypeVariables #-}
{-# LANGUAGE DataKinds, TypeOperators, AllowAmbiguousTypes #-}

-- | TypesettingRedex: Rule extraction interpreter for TypedRedex
--
-- Directly builds inference rules from relation definitions.
-- No intermediate AST - the structure IS the extraction.
module TypedRedex.Interp.Typesetting
  ( -- * Core types
    TypesettingRedex
  , ExtractedRule(..)
    -- * Running the interpreter
  , runTypesetting
  , runTypesettingWith
    -- * Formatting
  , formatRule
  , formatRuleWith
  , typesettingVar
    -- * Pretty-printing extracted rules (generic for any arity)
  , printRules
  , printRulesWith
  , ApplyTypesettingVars(..)
  ) where

import TypedRedex.Core.Internal.Redex
import TypedRedex.Core.Internal.Logic
import TypedRedex.DSL.Fresh (LTerm)
import TypedRedex.Interp.Format (formatCon, formatConWith, intercalate, TermFormatter(..), DefaultTermFormatter(..), JudgmentFormatter(..))
import TypedRedex.Interp.PrettyPrint (VarNaming(..), LogicVarNaming(..), namingByTag, subscriptNum)
import TypedRedex.Interp.Subst (RedexFresh(..))
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
-- Typesetting Interpreter State
--------------------------------------------------------------------------------

data TypesettingState = TypesettingState
  { tsVarCounter :: Int
  , tsBuilder    :: RuleBuilder           -- ^ Current rule being built
  , tsRules      :: [ExtractedRule]       -- ^ Completed rules
  , tsDepth      :: Int                   -- ^ Expansion depth
  , tsFormatter  :: String -> [String] -> String
  }

initState :: TypesettingState
initState = initStateWith formatCon

initStateWith :: (String -> [String] -> String) -> TypesettingState
initStateWith fmt = TypesettingState 0 emptyBuilder [] 0 fmt

--------------------------------------------------------------------------------
-- Typesetting Redex Interpreter
--------------------------------------------------------------------------------

newtype TypesettingRedex a = TypesettingRedex (State TypesettingState a)
  deriving (Functor, Applicative, Monad, MonadState TypesettingState)

instance Alternative TypesettingRedex where
  empty = TypesettingRedex $ pure (error "TypesettingRedex: empty")
  a <|> b = do
    s0 <- get
    -- Run branch a
    put $ s0 { tsBuilder = emptyBuilder, tsRules = [] }
    _ <- a
    rulesA <- gets tsRules
    builderA <- gets tsBuilder
    let rulesA' = if null (rbName builderA) then rulesA else finishRule builderA : rulesA
    -- Run branch b
    put $ s0 { tsBuilder = emptyBuilder, tsRules = [] }
    _ <- b
    rulesB <- gets tsRules
    builderB <- gets tsBuilder
    let rulesB' = if null (rbName builderB) then rulesB else finishRule builderB : rulesB
    -- Combine rules
    put $ s0 { tsRules = tsRules s0 ++ reverse rulesA' ++ reverse rulesB' }
    pure (error "TypesettingRedex: <|> result")

--------------------------------------------------------------------------------
-- Redex Instance
--------------------------------------------------------------------------------

instance Redex TypesettingRedex where
  newtype RVar TypesettingRedex t = TVar Int
    deriving (Functor)

  fresh_ FreshVar k = do
    n <- gets tsVarCounter
    modify $ \s -> s { tsVarCounter = n + 1 }
    k (Var (TVar n))
  fresh_ (ArgVar (Free v)) k = k v
  fresh_ (ArgVar (Ground _)) k = do
    n <- gets tsVarCounter
    modify $ \s -> s { tsVarCounter = n + 1 }
    k (Var (TVar n))

  unify x y = do
    inConcl <- gets (rbInConclusion . tsBuilder)
    when inConcl $ do
      fmt <- gets tsFormatter
      -- Capture x (the pattern/term), not y (the fresh variable)
      let pattern = prettyLFmt fmt x
      modify $ \s -> s { tsBuilder = (tsBuilder s) { rbPatterns = pattern : rbPatterns (tsBuilder s) } }

  suspend = id

  call_ _ rel = do
    depth <- gets tsDepth
    if depth == 0
      then do
        -- Depth 0→1: This is a rule call, set the rule name
        modify $ \s -> s { tsBuilder = (tsBuilder s) { rbName = relName rel }, tsDepth = 1 }
        relBody rel
        modify $ \s -> s { tsDepth = 0 }
      else
        -- Depth > 0: Inside rule body, don't expand further
        pure ()

  displayVar (TVar n) = "e" ++ subscriptNum n

  markConclusion = modify $ \s ->
    s { tsBuilder = (tsBuilder s) { rbInConclusion = True } }

  markPremise name args = do
    argStrs <- mapM prettyCaptured args
    modify $ \s -> s { tsBuilder = (tsBuilder s) {
      rbPremises = (name, argStrs) : rbPremises (tsBuilder s)
    } }

  -- Skip lifted actions since we're just extracting rule structure
  skipLiftedActions _ = True

prettyCaptured :: CapturedTerm TypesettingRedex -> TypesettingRedex String
prettyCaptured (CapturedTerm term) = do
  fmt <- gets tsFormatter
  pure $ prettyLFmt fmt term

instance EqVar TypesettingRedex where
  varEq (TVar a) (TVar b) = a == b

-- | Negation-as-failure is a no-op for rule extraction.
-- We're just extracting rule structure, not executing.
instance RedexNeg TypesettingRedex where
  neg _ = pure ()

-- | Fresh integer generation for nominal atoms.
-- TypesettingRedex reuses the variable counter for fresh integers.
instance RedexFresh TypesettingRedex where
  freshInt = do
    n <- gets tsVarCounter
    modify $ \s -> s { tsVarCounter = n + 1 }
    pure n

-- | Evaluation is a no-op for rule extraction.
-- This should never be called since we skip lifted actions.
instance RedexEval TypesettingRedex where
  derefVar _ = error "TypesettingRedex: derefVar should not be called during rule extraction"

--------------------------------------------------------------------------------
-- Pretty-printing Logic terms
--------------------------------------------------------------------------------

prettyLFmt :: forall a. LogicType a => (String -> [String] -> String) -> Logic a (RVar TypesettingRedex) -> String
prettyLFmt _ (Free v) =
  case unVar v of
    TVar n -> "«" ++ vnTag (varNaming @a) ++ ":" ++ show n ++ "»"
prettyLFmt fmt (Ground r) = prettyReifiedFmt fmt r

prettyReifiedFmt :: LogicType a => (String -> [String] -> String) -> Reified a (RVar TypesettingRedex) -> String
prettyReifiedFmt fmt r =
  let (con, fields) = quote r
  in fmt (constructorName con) (map (prettyFieldFmt fmt) fields)

prettyFieldFmt :: (String -> [String] -> String) -> Field a (RVar TypesettingRedex) -> String
prettyFieldFmt fmt (Field _ logic) = prettyLogicAnyFmt fmt logic

prettyLogicAnyFmt :: forall t. LogicType t => (String -> [String] -> String) -> Logic t (RVar TypesettingRedex) -> String
prettyLogicAnyFmt _ (Free v) =
  case unVar v of
    TVar n -> "«" ++ vnTag (varNaming @t) ++ ":" ++ show n ++ "»"
prettyLogicAnyFmt fmt (Ground r) = prettyReifiedFmt fmt r

--------------------------------------------------------------------------------
-- Running and extracting
--------------------------------------------------------------------------------

-- | Run a TypesettingRedex computation and extract all rules
runTypesetting :: TypesettingRedex () -> [ExtractedRule]
runTypesetting = runTypesettingWith DefaultTermFormatter

-- | Run with a custom formatter
runTypesettingWith :: TermFormatter fmt => fmt -> TypesettingRedex () -> [ExtractedRule]
runTypesettingWith fmt (TypesettingRedex m) =
  let finalState = execState m (initStateWith (formatConWith fmt))
      builder = tsBuilder finalState
      rules = tsRules finalState
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
typesettingVar :: Int -> Logic a (RVar TypesettingRedex)
typesettingVar n = Free (Var (TVar n))

--------------------------------------------------------------------------------
-- Applying typesettingVar to curried functions
--------------------------------------------------------------------------------

-- | Type class for applying typesettingVar with incrementing indices to curried functions.
-- This allows a single generic printRules to work for any arity.
class ApplyTypesettingVars ts where
  applyTypesettingVarsTo :: Proxy ts -> Int -> CurriedR TypesettingRedex ts result -> result

instance ApplyTypesettingVars '[] where
  applyTypesettingVarsTo _ _ r = r

instance (LogicType t, ApplyTypesettingVars ts) => ApplyTypesettingVars (t ': ts) where
  applyTypesettingVarsTo _ n f = applyTypesettingVarsTo (Proxy @ts) (n + 1) (f (typesettingVar n))

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
printRules :: forall ts. ApplyTypesettingVars ts
           => String
           -> CurriedR TypesettingRedex ts (Applied TypesettingRedex ts)
           -> IO ()
printRules judgmentName rel = do
  let applied :: Applied TypesettingRedex ts
      applied = applyTypesettingVarsTo (Proxy @ts) 0 rel
  let rules = runTypesetting $ appGoal applied
  mapM_ (\r -> putStrLn (formatRuleWith judgmentName r) >> putStrLn "") rules

-- | Print extracted rules with a custom formatter.
printRulesWith :: forall ts fmt. (ApplyTypesettingVars ts, TermFormatter fmt, JudgmentFormatter fmt)
               => fmt
               -> String
               -> CurriedR TypesettingRedex ts (Applied TypesettingRedex ts)
               -> IO ()
printRulesWith fmt judgmentName rel = do
  let applied :: Applied TypesettingRedex ts
      applied = applyTypesettingVarsTo (Proxy @ts) 0 rel
  let rules = runTypesettingWith fmt $ appGoal applied
  mapM_ (\r -> putStrLn (formatRule fmt judgmentName r) >> putStrLn "") rules
