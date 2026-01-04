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
--   (VarRef with            (DisplayVar with      (Uses HasDisplay:
--    internal IDs)           display numbers)      typeNaming + formatCon)
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

import TypedRedex.Logic
import TypedRedex.Logic.Display (VarNames)
import TypedRedex.DSL.Define (Applied(..))
import TypedRedex.DSL.Moded (T(..), AppliedM(..), toApplied, ground)
import Control.Monad (when, forM)
import Control.Monad.State
import Data.Proxy (Proxy(..))
import Data.Typeable (TypeRep, typeRep)
import qualified Data.Map.Strict as M
import qualified Data.Set as S

--------------------------------------------------------------------------------
-- Structural Representations
--------------------------------------------------------------------------------

-- | Variable reference with internal ID and type information.
data VarRef = VarRef
  { vrId      :: Int      -- ^ Internal variable ID (from fresh)
  , vrTypeRep :: TypeRep  -- ^ Type for naming lookup
  , vrNaming  :: VarNames -- ^ Naming scheme (from HasDisplay)
  }

instance Eq VarRef where
  VarRef aId aTy _ == VarRef bId bTy _ = aId == bId && aTy == bTy

instance Ord VarRef where
  compare (VarRef aId aTy _) (VarRef bId bTy _) =
    compare (aTy, aId) (bTy, bId)

instance Show VarRef where
  show (VarRef n tyRep _) = "VarRef " ++ show n ++ " " ++ show tyRep

-- | Raw term: structural representation before renumbering.
--
-- Produced by the typesetting interpreter.
data RawTerm
  = RVar VarRef              -- ^ A logic variable
  | RCon
      { rtConName     :: String
      , rtConFormat   :: String -> [String] -> Maybe String
      , rtConChildren :: [RawTerm]
      }

instance Eq RawTerm where
  RVar a == RVar b = a == b
  RCon nameA _ kidsA == RCon nameB _ kidsB = nameA == nameB && kidsA == kidsB
  _ == _ = False

instance Show RawTerm where
  show (RVar v) = show v
  show (RCon name _ kids) = "RCon " ++ show name ++ " " ++ show kids

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
  , dvNaming  :: VarNames -- ^ Naming scheme (from HasDisplay)
  }

instance Eq DisplayVar where
  DisplayVar aNum aTy _ == DisplayVar bNum bTy _ = aNum == bNum && aTy == bTy

instance Show DisplayVar where
  show (DisplayVar n tyRep _) = "DisplayVar " ++ show n ++ " " ++ show tyRep

-- | Display term: after renumbering.
data DisplayTerm
  = DVar DisplayVar            -- ^ A display variable
  | DCon
      { dtConName     :: String
      , dtConFormat   :: String -> [String] -> Maybe String
      , dtConChildren :: [DisplayTerm]
      }

instance Eq DisplayTerm where
  DVar a == DVar b = a == b
  DCon nameA _ kidsA == DCon nameB _ kidsB = nameA == nameB && kidsA == kidsB
  _ == _ = False

instance Show DisplayTerm where
  show (DVar v) = show v
  show (DCon name _ kids) = "DCon " ++ show name ++ " " ++ show kids

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
  , rbPremises    :: [(String, [CapturedTerm TypesettingRedex], [String] -> String)]  -- ^ Deferred premises (reverse order)
  }

emptyBuilder :: RuleBuilder
emptyBuilder = RuleBuilder "" False [] defaultFmt []
  where defaultFmt args = intercalate ", " args
        intercalate _ [] = ""
        intercalate _ [x] = x
        intercalate sep (x:xs) = x ++ sep ++ intercalate sep xs

-- | Finish building a rule, capturing premises with the current substitution.
--
-- This must be called after the conclusion has established bindings, so that
-- premises resolve variables consistently with the conclusion.
finishRuleM :: RuleBuilder -> TypesettingRedex RawRule
finishRuleM rb = do
  capturedPremises <- forM (reverse (rbPremises rb)) $ \(name, args, fmt) -> do
    argTerms <- mapM captureCapturedM args
    pure (name, argTerms, fmt)
  pure $ RawRule
    { rrName = rbName rb
    , rrConclusion = reverse (rbConclusion rb)
    , rrConclFmt = rbConclFmt rb
    , rrPremises = capturedPremises
    }

--------------------------------------------------------------------------------
-- Typesetting Interpreter State
--------------------------------------------------------------------------------

data TypesettingState = TypesettingState
  { tsVarCounter :: Int
  , tsBuilder    :: RuleBuilder
  , tsRules      :: [RawRule]
  , tsDepth      :: Int
  , tsSubst      :: M.Map VarRef RawTerm
  }

-- | Reserve low IDs for the caller-provided argument variables (modedVar 0,1,...)
-- so rule-local fresh variables don't collide with them.
initialVarCounter :: Int
initialVarCounter = 1000

initState :: TypesettingState
initState = TypesettingState initialVarCounter emptyBuilder [] 0 M.empty

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
    put $ s0 { tsBuilder = emptyBuilder, tsRules = [], tsVarCounter = initialVarCounter, tsSubst = M.empty }
    _ <- a
    rulesA <- gets tsRules
    builderA <- gets tsBuilder
    rulesA' <- if null (rbName builderA)
               then pure rulesA
               else do
                 finished <- finishRuleM builderA
                 pure (rulesA ++ [finished])
    -- Run branch b
    put $ s0 { tsBuilder = emptyBuilder, tsRules = [], tsVarCounter = initialVarCounter, tsSubst = M.empty }
    _ <- b
    rulesB <- gets tsRules
    builderB <- gets tsBuilder
    rulesB' <- if null (rbName builderB)
               then pure rulesB
               else do
                 finished <- finishRuleM builderB
                 pure (rulesB ++ [finished])
    -- Combine rules (in order: existing, then a, then b)
    put $ s0 { tsRules = tsRules s0 ++ rulesA' ++ rulesB' }
    pure (error "TypesettingRedex: <|> result")

--------------------------------------------------------------------------------
-- Pattern Capture (Logic term → RawTerm)
--------------------------------------------------------------------------------

-- | Resolve a RawTerm through the current substitution map.
resolveRaw :: M.Map VarRef RawTerm -> S.Set VarRef -> RawTerm -> RawTerm
resolveRaw subst visited t0 =
  case t0 of
    RVar v
      | S.member v visited -> RVar v
      | otherwise ->
          case M.lookup v subst of
            Nothing -> RVar v
            Just t  -> resolveRaw subst (S.insert v visited) t
    RCon name fmt children ->
      RCon name fmt (map (resolveRaw subst visited) children)

-- | Capture a logic term as a RawTerm, following recorded substitutions.
capturePatternWith :: forall a. LogicType a
                   => M.Map VarRef RawTerm
                   -> S.Set VarRef
                   -> Logic a (RVar TypesettingRedex)
                   -> RawTerm
capturePatternWith subst visited (Free v) =
  let TVar n = unVar v
      vr = VarRef n (typeRep (Proxy @a)) (typeNaming @a)
  in case M.lookup vr subst of
       Nothing -> RVar vr
       Just t  -> resolveRaw subst (S.insert vr visited) t
capturePatternWith subst visited (Ground r) =
  let (name, fields) = quote r
      children = map (captureFieldWith subst visited) fields
  in RCon name (formatCon @a) children

-- | Capture a field (existential wrapper).
captureFieldWith :: M.Map VarRef RawTerm -> S.Set VarRef -> Field a (RVar TypesettingRedex) -> RawTerm
captureFieldWith subst visited (Field (proxy :: Proxy t) logic) =
  capturePatternAnyWith subst visited proxy logic

-- | Capture any logic term.
capturePatternAnyWith :: forall t. LogicType t
                      => M.Map VarRef RawTerm
                      -> S.Set VarRef
                      -> Proxy t
                      -> Logic t (RVar TypesettingRedex)
                      -> RawTerm
capturePatternAnyWith subst visited _ = capturePatternWith @t subst visited

capturePatternM :: forall a. LogicType a
                => Logic a (RVar TypesettingRedex)
                -> TypesettingRedex RawTerm
capturePatternM term = do
  subst <- gets tsSubst
  pure $ capturePatternWith @a subst S.empty term

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
    -- Record simple bindings (for typesetting-only unification), so helper
    -- operations like binder opening can expose structure without forcing eval.
    recordBinding x y

    inConcl <- gets (rbInConclusion . tsBuilder)
    when inConcl $ do
      pattern <- capturePatternM x
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
    -- Don't capture immediately; store CapturedTerms for deferred capture
    -- after the conclusion establishes bindings
    modify $ \s -> s { tsBuilder = (tsBuilder s) {
      rbPremises = (name, args, fmt) : rbPremises (tsBuilder s)
    } }

  skipLiftedActions _ = True

-- | Capture a CapturedTerm as RawTerm.
captureCapturedM :: CapturedTerm TypesettingRedex -> TypesettingRedex RawTerm
captureCapturedM (CapturedTerm term) = capturePatternM term

-- | Record a binding @v := term@ for the typesetting interpreter.
--
-- This is intentionally incomplete (no occurs check, no deep unification);
-- it exists only so the rule printer can follow structural equalities.
recordBinding :: forall a. LogicType a
              => Logic a (RVar TypesettingRedex)
              -> Logic a (RVar TypesettingRedex)
              -> TypesettingRedex ()
recordBinding (Free v) t = bindIfUnbound @a v t
recordBinding t (Free v) = bindIfUnbound @a v t
recordBinding _ _ = pure ()

bindIfUnbound :: forall a. LogicType a
              => Var a (RVar TypesettingRedex)
              -> Logic a (RVar TypesettingRedex)
              -> TypesettingRedex ()
bindIfUnbound v t =
  case t of
    Free v'
      | varEq (unVar v) (unVar v') -> pure ()  -- avoid v := v
      | otherwise -> bind
    _ -> bind
  where
    bind = do
      subst <- gets tsSubst
      let TVar n = unVar v
          key = VarRef n (typeRep (Proxy @a)) (typeNaming @a)
      case M.lookup key subst of
        Just _  -> pure ()  -- don't overwrite existing bindings
        Nothing -> do
          rhs <- capturePatternM @a t
          modify $ \s -> s { tsSubst = M.insert key rhs (tsSubst s) }

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
runTypesetting goal =
  let TypesettingRedex action = do
        _ <- goal
        builder <- gets tsBuilder
        when (not $ null $ rbName builder) $ do
          finished <- finishRuleM builder
          modify $ \s -> s { tsRules = tsRules s ++ [finished] }
      (_, finalState) = runState action initState
  in tsRules finalState

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
collectVars (RCon _ _ children) = concatMap collectVars children

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
  in DVar (DisplayVar displayNum (vrTypeRep v) (vrNaming v))
applyVarMap m (RCon name fmt children) =
  DCon name fmt (map (applyVarMap m) children)

--------------------------------------------------------------------------------
-- Formatting
--------------------------------------------------------------------------------

-- | Format a display variable using its naming scheme.
formatVar :: DisplayVar -> String
formatVar (DisplayVar n _ names) = names !! n  -- Safe: VarNames is infinite

-- | Format a display term to a string.
formatDisplayTerm :: DisplayTerm -> String
formatDisplayTerm (DVar dv) = formatVar dv
formatDisplayTerm (DCon name fmt children) =
  let childStrs = map formatDisplayTerm children
  in case fmt name childStrs of
       Just s  -> s
       Nothing -> defaultFormatCon name childStrs

-- | Format a display rule as an ASCII inference rule.
--
-- Uses the format functions stored in the rule itself (from judgment definitions).
formatRule :: DisplayRule -> String
formatRule rule =
  let conclStrs = map formatDisplayTerm (drConclusion rule)
      conclusion = drConclFmt rule conclStrs
      prems = map (\(_, pargs, pfmt) ->
                     pfmt (map formatDisplayTerm pargs))
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
-- printRules $ appGoal applied
-- @
printRules :: TypesettingRedex () -> IO ()
printRules goal = do
  let rawRules = runTypesetting goal
      displayRules = map renumber rawRules
  mapM_ (\r -> putStrLn (formatRule r) >> putStrLn "") displayRules

--------------------------------------------------------------------------------
-- Support for moded judgments
--------------------------------------------------------------------------------

-- | Convert an AppliedM (from moded judgment) to Applied (for typesetting).
modedToApplied :: AppliedM TypesettingRedex name modes vss ts -> Applied TypesettingRedex ts
modedToApplied = toApplied

-- | Create a ground moded term for typesetting.
modedVar :: LogicType a => Int -> T '[] a TypesettingRedex
modedVar n = ground (typesettingVar n)
