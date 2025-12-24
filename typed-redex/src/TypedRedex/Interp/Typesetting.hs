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
    -- * Support for moded judgments
  , modedToApplied
  , modedVar
  ) where

import TypedRedex.Core.Internal.Redex
import TypedRedex.Core.Internal.Logic
import TypedRedex.DSL.Fresh (LTerm)
import TypedRedex.Interp.Format (formatCon, formatConWith, intercalate, TermFormatter(..), DefaultTermFormatter(..), JudgmentFormatter(..))
import TypedRedex.Interp.PrettyPrint (TypesetNaming(..), subscriptNum)
import TypedRedex.Interp.Subst (RedexFresh(..))
import TypedRedex.Nominal.Hash (RedexHash(..))
import TypedRedex.DSL.Define (Applied(..), CurriedR)
import TypedRedex.DSL.Moded (T(..), AppliedM(..), toApplied, ground)
import Control.Applicative
import Control.Monad (when)
import Control.Monad.State
import Data.Proxy (Proxy(..))
import Data.Typeable (TypeRep, Typeable, typeRep)
import qualified Data.Map.Strict as M

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
  -- Eager renumbering state (per-rule, reset on each rule)
  , tsVarMap     :: M.Map (TypeRep, Int) Int  -- ^ (type, internalId) -> displayNum
  , tsVarCounts  :: M.Map TypeRep Int         -- ^ Next display number per type
  }

initState :: TypesettingState
initState = initStateWith formatCon

initStateWith :: (String -> [String] -> String) -> TypesettingState
initStateWith fmt = TypesettingState 0 emptyBuilder [] 0 fmt M.empty M.empty

-- | Reset renumbering state (called at start of each rule)
resetRenumbering :: TypesettingState -> TypesettingState
resetRenumbering s = s { tsVarMap = M.empty, tsVarCounts = M.empty }

--------------------------------------------------------------------------------
-- Typesetting Redex Interpreter
--------------------------------------------------------------------------------

newtype TypesettingRedex a = TypesettingRedex (State TypesettingState a)
  deriving (Functor, Applicative, Monad, MonadState TypesettingState)

instance Alternative TypesettingRedex where
  empty = TypesettingRedex $ pure (error "TypesettingRedex: empty")
  a <|> b = do
    s0 <- get
    -- Run branch a (reset renumbering for fresh variable names)
    put $ resetRenumbering $ s0 { tsBuilder = emptyBuilder, tsRules = [] }
    _ <- a
    rulesA <- gets tsRules
    builderA <- gets tsBuilder
    let rulesA' = if null (rbName builderA) then rulesA else finishRule builderA : rulesA
    -- Run branch b (reset renumbering for fresh variable names)
    put $ resetRenumbering $ s0 { tsBuilder = emptyBuilder, tsRules = [] }
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
      pattern <- prettyLFmt fmt x
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
  prettyLFmt fmt term

instance EqVar TypesettingRedex where
  varEq (TVar a) (TVar b) = a == b

-- | Negation-as-failure is a no-op for rule extraction.
-- We're just extracting rule structure, not executing.
instance RedexNeg TypesettingRedex where
  neg _ = pure ()

-- | Hash (freshness constraint) is a no-op for rule extraction.
-- We're just extracting rule structure, not executing.
instance RedexHash TypesettingRedex where
  hash _ _ = pure ()

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
-- Eager variable renumbering
--------------------------------------------------------------------------------

-- | Get or assign a display number for a variable.
-- Uses TypeRep as the type identifier for the renumbering map.
getDisplayNum :: forall a. Typeable a => Int -> TypesettingRedex Int
getDisplayNum internalId = do
  let tyRep = typeRep (Proxy @a)
  varMap <- gets tsVarMap
  case M.lookup (tyRep, internalId) varMap of
    Just displayNum -> pure displayNum
    Nothing -> do
      -- First occurrence: assign next display number for this type
      counts <- gets tsVarCounts
      let displayNum = M.findWithDefault 0 tyRep counts
      modify $ \s -> s
        { tsVarMap = M.insert (tyRep, internalId) displayNum (tsVarMap s)
        , tsVarCounts = M.insert tyRep (displayNum + 1) (tsVarCounts s)
        }
      pure displayNum

--------------------------------------------------------------------------------
-- Pretty-printing Logic terms (monadic, with eager renumbering)
--------------------------------------------------------------------------------

prettyLFmt :: forall a. (LogicType a, TypesetNaming a, Typeable a)
           => (String -> [String] -> String)
           -> Logic a (RVar TypesettingRedex)
           -> TypesettingRedex String
prettyLFmt _ (Free v) = do
  case unVar v of
    TVar n -> do
      displayNum <- getDisplayNum @a n
      pure $ typesetName @a displayNum
prettyLFmt fmt (Ground r) = prettyReifiedFmt fmt r

prettyReifiedFmt :: (LogicType a, Typeable a)
                 => (String -> [String] -> String)
                 -> Reified a (RVar TypesettingRedex)
                 -> TypesettingRedex String
prettyReifiedFmt fmt r = do
  let (name, fields) = quote r
  fieldStrs <- mapM (prettyFieldFmt fmt) fields
  pure $ fmt name fieldStrs

prettyFieldFmt :: (String -> [String] -> String)
               -> Field a (RVar TypesettingRedex)
               -> TypesettingRedex String
prettyFieldFmt fmt (Field _ logic) = prettyLogicAnyFmt fmt logic

prettyLogicAnyFmt :: forall t. (LogicType t, TypesetNaming t, Typeable t)
                  => (String -> [String] -> String)
                  -> Logic t (RVar TypesettingRedex)
                  -> TypesettingRedex String
prettyLogicAnyFmt _ (Free v) = do
  case unVar v of
    TVar n -> do
      displayNum <- getDisplayNum @t n
      pure $ typesetName @t displayNum
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
-- Formatting rules
--------------------------------------------------------------------------------

-- | Format an extracted rule as ASCII inference rule.
-- No post-processing needed - variable names are already resolved.
formatRule :: JudgmentFormatter fmt => fmt -> String -> ExtractedRule -> String
formatRule fmt judgmentName rule =
  let conclusion = formatJudgment fmt judgmentName (erPatterns rule)
      prems = map (\(pname, pargs) -> formatJudgment fmt pname pargs) (erPremises rule)
      maxLen = maximum $ length conclusion : map length prems
      line = replicate (maxLen + 4) '─'
  in (if null prems then "" else unlines (map ("  " ++) prems)) ++
     "  " ++ line ++ " [" ++ erName rule ++ "]\n" ++
     "  " ++ conclusion

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

--------------------------------------------------------------------------------
-- Support for moded judgments
--------------------------------------------------------------------------------

-- | Convert an AppliedM (from moded judgment) to Applied (for typesetting).
--
-- Re-export of 'toApplied' for convenience.
modedToApplied :: AppliedM TypesettingRedex name modes vss ts -> Applied TypesettingRedex ts
modedToApplied = toApplied

-- | Create a ground moded term for typesetting.
--
-- Use this to create arguments for moded judgments when typesetting:
--
-- @
-- let applied = modedToApplied $ ssub (modedVar 0) (modedVar 1) (modedVar 2) ...
-- @
modedVar :: LogicType a => Int -> T '[] a TypesettingRedex
modedVar n = ground (typesettingVar n)
