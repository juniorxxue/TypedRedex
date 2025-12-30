{-# LANGUAGE TypeFamilies, GeneralisedNewtypeDeriving, DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, FlexibleContexts #-}
{-# LANGUAGE GADTs, RankNTypes, TypeApplications, ScopedTypeVariables #-}
{-# LANGUAGE DataKinds, TypeOperators, AllowAmbiguousTypes #-}

-- | TypesettingRedex: Rule extraction interpreter for TypedRedex
--
-- Extracts inference rules from relation definitions using a structural
-- intermediate representation. Rules are captured as 'RawRule', then
-- renumbered to 'DisplayRule', and finally formatted to strings.
--
-- = Pipeline
--
-- @
-- TypesettingRedex          renumber              format
--      │                       │                    │
--      ▼                       ▼                    ▼
--   RawRule    ────────►  DisplayRule  ────────►  String
--
--   (VarRef with            (DisplayVar with      (Uses TermFormatter +
--    internal IDs)           display numbers)      NamingConfig)
-- @
module TypedRedex.Interp.Typesetting
  ( -- * Core types
    TypesettingRedex
    -- * Structural representations
  , VarRef(..)
  , RawTerm(..)
  , RawRule(..)
  , DisplayVar(..)
  , DisplayTerm(..)
  , DisplayRule(..)
    -- * Running the interpreter
  , runTypesetting
    -- * Renumbering (conclusion-first ordering)
  , renumber
    -- * Formatting
  , formatRule
  , formatDisplayTerm
    -- * Pretty-printing extracted rules
  , printRules
  , typesettingVar
    -- * Support for moded judgments
  , modedToApplied
  , modedVar
  ) where

import TypedRedex.Logic hiding (defaultFormatCon)
import TypedRedex.Interp.Format (TermFormatter(..), DefaultTermFormatter(..))
import TypedRedex.Interp.PrettyPrint (NamingConfig, lookupNaming, subscriptNum, emptyNaming)
import TypedRedex.DSL.Define (Applied(..), appGoal)
import TypedRedex.DSL.Moded (T(..), AppliedM(..), toApplied, ground)
import Control.Monad (when)
import Control.Monad.State
import Data.Proxy (Proxy(..))
import Data.Typeable (TypeRep, Typeable, typeRep)
import qualified Data.Map.Strict as M
import Control.Applicative (Alternative(..))

--------------------------------------------------------------------------------
-- Structural Representations
--------------------------------------------------------------------------------

-- | Variable reference with internal ID and type information.
data VarRef = VarRef
  { vrId      :: Int      -- ^ Internal variable ID (from fresh)
  , vrTypeRep :: TypeRep  -- ^ Type for naming lookup
  } deriving (Eq, Ord, Show)

-- | Raw term: structural representation before renumbering.
--
-- Produced by the typesetting interpreter.
data RawTerm
  = RVar VarRef              -- ^ A logic variable
  | RCon String [RawTerm]    -- ^ Constructor with name and children
  deriving (Show, Eq)

-- | Raw rule: structural representation before renumbering.
data RawRule = RawRule
  { rrName       :: String                    -- ^ Rule name
  , rrConclusion :: [RawTerm]                 -- ^ Conclusion pattern arguments
  , rrConclFmt   :: [String] -> String        -- ^ Conclusion format function
  , rrPremises   :: [(String, [RawTerm], [String] -> String)]  -- ^ (judgment name, arguments, format)
  }

-- | Display variable: after renumbering, with display index.
data DisplayVar = DisplayVar
  { dvNum     :: Int      -- ^ Display number (0, 1, 2, ...)
  , dvTypeRep :: TypeRep  -- ^ Type for naming lookup
  } deriving (Show, Eq)

-- | Display term: after renumbering.
data DisplayTerm
  = DVar DisplayVar            -- ^ A display variable
  | DCon String [DisplayTerm]  -- ^ Constructor with name and children
  deriving (Show, Eq)

-- | Display rule: after renumbering, ready for formatting.
data DisplayRule = DisplayRule
  { drName       :: String
  , drConclusion :: [DisplayTerm]
  , drConclFmt   :: [String] -> String        -- ^ Conclusion format function
  , drPremises   :: [(String, [DisplayTerm], [String] -> String)]  -- ^ (name, args, format)
  }

--------------------------------------------------------------------------------
-- Rule Builder (state during extraction)
--------------------------------------------------------------------------------

data RuleBuilder = RuleBuilder
  { rbName        :: String
  , rbInConclusion :: Bool
  , rbConclusion  :: [RawTerm]                 -- ^ Conclusion patterns (reverse order)
  , rbConclFmt    :: [String] -> String        -- ^ Conclusion format function
  , rbPremises    :: [(String, [RawTerm], [String] -> String)]  -- ^ Premises (reverse order)
  }

emptyBuilder :: RuleBuilder
emptyBuilder = RuleBuilder "" False [] defaultFmt []
  where defaultFmt args = intercalate ", " args
        intercalate _ [] = ""
        intercalate _ [x] = x
        intercalate sep (x:xs) = x ++ sep ++ intercalate sep xs

finishRule :: RuleBuilder -> RawRule
finishRule rb = RawRule
  { rrName = rbName rb
  , rrConclusion = reverse (rbConclusion rb)
  , rrConclFmt = rbConclFmt rb
  , rrPremises = reverse (rbPremises rb)
  }

--------------------------------------------------------------------------------
-- Typesetting Interpreter State
--------------------------------------------------------------------------------

data TypesettingState = TypesettingState
  { tsVarCounter :: Int
  , tsBuilder    :: RuleBuilder
  , tsRules      :: [RawRule]
  , tsDepth      :: Int
  }

initState :: TypesettingState
initState = TypesettingState 0 emptyBuilder [] 0

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
    put $ s0 { tsBuilder = emptyBuilder, tsRules = [], tsVarCounter = 0 }
    _ <- a
    rulesA <- gets tsRules
    builderA <- gets tsBuilder
    let rulesA' = if null (rbName builderA) then rulesA else rulesA ++ [finishRule builderA]
    -- Run branch b
    put $ s0 { tsBuilder = emptyBuilder, tsRules = [], tsVarCounter = 0 }
    _ <- b
    rulesB <- gets tsRules
    builderB <- gets tsBuilder
    let rulesB' = if null (rbName builderB) then rulesB else rulesB ++ [finishRule builderB]
    -- Combine rules (in order: existing, then a, then b)
    put $ s0 { tsRules = tsRules s0 ++ rulesA' ++ rulesB' }
    pure (error "TypesettingRedex: <|> result")

--------------------------------------------------------------------------------
-- Pattern Capture (Logic term → RawTerm)
--------------------------------------------------------------------------------

-- | Capture a logic term as a RawTerm.
capturePattern :: forall a. (LogicType a, Typeable a)
               => Logic a (RVar TypesettingRedex)
               -> RawTerm
capturePattern (Free v) =
  let TVar n = unVar v
  in RVar (VarRef n (typeRep (Proxy @a)))
capturePattern (Ground r) =
  let (name, fields) = quote r
      children = map captureField fields
  in RCon name children

-- | Capture a field (existential wrapper).
captureField :: Field a (RVar TypesettingRedex) -> RawTerm
captureField (Field (proxy :: Proxy t) logic) =
  capturePatternAny proxy logic

-- | Capture any logic term (dispatches by Typeable).
capturePatternAny :: forall t. (LogicType t, Typeable t)
                  => Proxy t
                  -> Logic t (RVar TypesettingRedex)
                  -> RawTerm
capturePatternAny _ = capturePattern @t

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

  unify x _ = do
    inConcl <- gets (rbInConclusion . tsBuilder)
    when inConcl $ do
      let pattern = capturePattern x
      modify $ \s -> s { tsBuilder = (tsBuilder s)
        { rbConclusion = pattern : rbConclusion (tsBuilder s) } }

  suspend = id

  call_ _ rel = do
    depth <- gets tsDepth
    if depth == 0
      then do
        modify $ \s -> s { tsBuilder = (tsBuilder s) { rbName = relRule rel, rbConclFmt = relFormat rel }, tsDepth = 1 }
        relBody rel
        modify $ \s -> s { tsDepth = 0 }
      else
        pure ()

  displayVar (TVar n) = "v" ++ show n

  markConclusion = modify $ \s ->
    s { tsBuilder = (tsBuilder s) { rbInConclusion = True } }

  markPremise name args fmt = do
    argTerms <- pure $ map captureCaptured args
    modify $ \s -> s { tsBuilder = (tsBuilder s) {
      rbPremises = (name, argTerms, fmt) : rbPremises (tsBuilder s)
    } }

  skipLiftedActions _ = True

-- | Capture a CapturedTerm as RawTerm.
captureCaptured :: CapturedTerm TypesettingRedex -> RawTerm
captureCaptured (CapturedTerm term) = capturePattern term

instance EqVar TypesettingRedex where
  varEq (TVar a) (TVar b) = a == b

instance RedexNeg TypesettingRedex where
  neg _ = pure ()

instance RedexHash TypesettingRedex where
  hash _ _ = pure ()

instance RedexFresh TypesettingRedex where
  freshInt = do
    n <- gets tsVarCounter
    modify $ \s -> s { tsVarCounter = n + 1 }
    pure n

instance RedexEval TypesettingRedex where
  derefVar _ = error "TypesettingRedex: derefVar should not be called"

--------------------------------------------------------------------------------
-- Running the Interpreter
--------------------------------------------------------------------------------

-- | Run a TypesettingRedex computation and extract all raw rules.
runTypesetting :: TypesettingRedex () -> [RawRule]
runTypesetting (TypesettingRedex m) =
  let finalState = execState m initState
      builder = tsBuilder finalState
      rules = tsRules finalState
  in if null (rbName builder)
     then rules
     else rules ++ [finishRule builder]

--------------------------------------------------------------------------------
-- Renumbering (conclusion-first ordering)
--------------------------------------------------------------------------------

-- | Renumber variables: conclusion first, then premises in order.
--
-- This ensures the first variable in the conclusion gets display number 0,
-- the second gets 1, and so on.
renumber :: RawRule -> DisplayRule
renumber raw =
  let -- Collect variables: conclusion first, then premises
      conclVars = concatMap collectVars (rrConclusion raw)
      premVars = concatMap (\(_, ts, _) -> concatMap collectVars ts) (rrPremises raw)
      allVars = conclVars ++ premVars

      -- Build renumbering map
      varMap = buildVarMap allVars

      -- Apply renumbering
      newConclusion = map (applyVarMap varMap) (rrConclusion raw)
      newPremises = map (\(n, ts, fmt) -> (n, map (applyVarMap varMap) ts, fmt)) (rrPremises raw)
  in DisplayRule (rrName raw) newConclusion (rrConclFmt raw) newPremises

-- | Collect all VarRefs from a RawTerm (in order of appearance).
collectVars :: RawTerm -> [VarRef]
collectVars (RVar v) = [v]
collectVars (RCon _ children) = concatMap collectVars children

-- | Build a map from VarRef to display number (per-type).
-- Each type gets its own counter: first Env→0, second Env→1, first Ty→0, etc.
buildVarMap :: [VarRef] -> M.Map VarRef Int
buildVarMap = fst . foldl go (M.empty, M.empty)
  where
    go (varMap, typeCounters) v
      | M.member v varMap = (varMap, typeCounters)
      | otherwise =
          let tyRep = vrTypeRep v
              nextForType = M.findWithDefault 0 tyRep typeCounters
          in ( M.insert v nextForType varMap
             , M.insert tyRep (nextForType + 1) typeCounters
             )

-- | Apply the variable map to convert RawTerm to DisplayTerm.
applyVarMap :: M.Map VarRef Int -> RawTerm -> DisplayTerm
applyVarMap m (RVar v) =
  let displayNum = M.findWithDefault 0 v m
  in DVar (DisplayVar displayNum (vrTypeRep v))
applyVarMap m (RCon name children) =
  DCon name (map (applyVarMap m) children)

--------------------------------------------------------------------------------
-- Formatting
--------------------------------------------------------------------------------

-- | Format a display variable using the naming configuration.
formatVar :: NamingConfig -> DisplayVar -> String
formatVar config (DisplayVar n tyRep) =
  let names = lookupNaming tyRep config
  in names !! n  -- Safe: VarNames is infinite

-- | Format a display term to a string.
formatDisplayTerm :: TermFormatter fmt => fmt -> NamingConfig -> DisplayTerm -> String
formatDisplayTerm _ config (DVar dv) = formatVar config dv
formatDisplayTerm fmt config (DCon name children) =
  let childStrs = map (formatDisplayTerm fmt config) children
  in case formatTerm fmt name childStrs of
       Just s  -> s
       Nothing -> defaultFormatCon name childStrs

-- | Default constructor formatting.
defaultFormatCon :: String -> [String] -> String
defaultFormatCon name [] = name
defaultFormatCon name args = name ++ "(" ++ intercalate ", " args ++ ")"
  where
    intercalate sep = foldr1 (\x y -> x ++ sep ++ y)

-- | Format a display rule as an ASCII inference rule.
--
-- Uses the format functions stored in the rule itself (from judgment definitions).
formatRule :: TermFormatter fmt
           => fmt -> NamingConfig -> DisplayRule -> String
formatRule fmt config rule =
  let conclStrs = map (formatDisplayTerm fmt config) (drConclusion rule)
      conclusion = drConclFmt rule conclStrs
      prems = map (\(_, pargs, pfmt) ->
                     pfmt (map (formatDisplayTerm fmt config) pargs))
                  (drPremises rule)
      maxLen = maximum $ length conclusion : map length prems
      line = replicate (maxLen + 4) '─'
  in (if null prems then "" else unlines (map ("  " ++) prems)) ++
     "  " ++ line ++ " [" ++ drName rule ++ "]\n" ++
     "  " ++ conclusion

--------------------------------------------------------------------------------
-- Helper for creating variables
--------------------------------------------------------------------------------

-- | Create a logic variable for rule extraction.
typesettingVar :: Int -> Logic a (RVar TypesettingRedex)
typesettingVar n = Free (Var (TVar n))

--------------------------------------------------------------------------------
-- Pretty-printing extracted rules
--------------------------------------------------------------------------------

-- | Extract and print rules for a judgment.
--
-- The format function is taken from the judgment definition itself,
-- so no JudgmentFormatter instance is needed.
--
-- @
-- printRules emptyNaming SsubFormatter $ appGoal applied
-- @
printRules :: TermFormatter fmt
           => NamingConfig
           -> fmt
           -> TypesettingRedex ()
           -> IO ()
printRules config fmt goal = do
  let rawRules = runTypesetting goal
      displayRules = map renumber rawRules
  mapM_ (\r -> putStrLn (formatRule fmt config r) >> putStrLn "") displayRules

--------------------------------------------------------------------------------
-- Support for moded judgments
--------------------------------------------------------------------------------

-- | Convert an AppliedM (from moded judgment) to Applied (for typesetting).
modedToApplied :: AppliedM TypesettingRedex name modes vss ts -> Applied TypesettingRedex ts
modedToApplied = toApplied

-- | Create a ground moded term for typesetting.
modedVar :: LogicType a => Int -> T '[] a TypesettingRedex
modedVar n = ground (typesettingVar n)
