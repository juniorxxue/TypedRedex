{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}

-- | Typesetting Interpreter for Indexed Free Monad DSL
--
-- This interpreter extracts inference rules from the AST without executing them.
-- It produces a structural representation that can be formatted as ASCII inference rules.
--
-- = Key Insight
--
-- With Free Monad, we can traverse the AST purely, without any effects.
-- This makes rule extraction trivial: just walk the tree and collect patterns.
--
-- = Pipeline
--
-- @
-- IxFree AST  ────►  RawRule  ────►  DisplayRule  ────►  String
--   pure data      structural       renumbered        formatted
-- @
module TypedRedex.Free.Interp.Typeset
  ( -- * Structural Representations
    VarRef(..)
  , RawTerm(..)
  , RawRule(..)
  , DisplayVar(..)
  , DisplayTerm(..)
  , DisplayRule(..)
    -- * Extraction
  , extractRule
  , extractRules
    -- * Renumbering
  , renumber
    -- * Formatting
  , formatRule
  , formatDisplayTerm
  ) where

import qualified Prelude
import Prelude hiding ((>>=), (>>), return)
import Data.Proxy (Proxy(..))
import Data.Typeable (TypeRep, Typeable, typeRep)
import qualified Data.Map.Strict as M

import TypedRedex.Logic (LogicType(..), Logic(..), RVar, Field(..))
import TypedRedex.Free.IxFree (IxFree(..))
import TypedRedex.Free.RuleF
import TypedRedex.Free.Schedule (St(..))
import TypedRedex.Free.Moded (ModedRule(..))

--------------------------------------------------------------------------------
-- Structural Representations
--------------------------------------------------------------------------------

-- | Variable reference with internal ID and type info
data VarRef = VarRef
  { vrId      :: Int
  , vrTypeRep :: TypeRep
  } deriving (Eq, Ord, Show)

-- | Raw term: structural representation before renumbering
data RawTerm
  = RVar VarRef
  | RCon String [RawTerm]
  deriving (Show, Eq)

-- | Raw rule: extracted from AST
data RawRule = RawRule
  { rrName       :: String
  , rrConclusion :: [RawTerm]
  , rrPremises   :: [(String, [RawTerm])]
  } deriving (Show)

-- | Display variable: after renumbering
data DisplayVar = DisplayVar
  { dvNum     :: Int
  , dvTypeRep :: TypeRep
  } deriving (Show, Eq)

-- | Display term: after renumbering
data DisplayTerm
  = DVar DisplayVar
  | DCon String [DisplayTerm]
  deriving (Show, Eq)

-- | Display rule: ready for formatting
data DisplayRule = DisplayRule
  { drName       :: String
  , drConclusion :: [DisplayTerm]
  , drPremises   :: [(String, [DisplayTerm])]
  } deriving (Show)

--------------------------------------------------------------------------------
-- Extraction State
--------------------------------------------------------------------------------

data ExtractState = ExtractState
  { esNextVar    :: Int
  , esConclusion :: [RawTerm]
  , esPremises   :: [(String, [RawTerm])]
  }

emptyExtract :: ExtractState
emptyExtract = ExtractState 0 [] []

--------------------------------------------------------------------------------
-- Pattern Capture
--------------------------------------------------------------------------------

-- | Capture a logic term as RawTerm
capturePattern :: forall a var. (LogicType a, Typeable a)
               => Int -> Logic a var -> (RawTerm, Int)
capturePattern nextVar (Free _) =
  (RVar (VarRef nextVar (typeRep (Proxy @a))), nextVar + 1)
capturePattern nextVar (Ground r) =
  let (name, fields) = quoteTypeset r
      (children, nextVar') = captureFields nextVar fields
  in (RCon name children, nextVar')

-- | Quote without the RVar type - for typesetting purposes
quoteTypeset :: LogicType a => Reified a var -> (String, [Field a var])
quoteTypeset = quote

-- | Capture multiple fields
captureFields :: Int -> [Field a var] -> ([RawTerm], Int)
captureFields nextVar [] = ([], nextVar)
captureFields nextVar (Field (_ :: Proxy t) logic : rest) =
  let (term, nextVar') = capturePatternAny @t nextVar logic
      (terms, nextVar'') = captureFields nextVar' rest
  in (term : terms, nextVar'')

-- | Capture any typed logic term
capturePatternAny :: forall t var. (LogicType t, Typeable t)
                  => Int -> Logic t var -> (RawTerm, Int)
capturePatternAny = capturePattern @t

--------------------------------------------------------------------------------
-- AST Extraction
--------------------------------------------------------------------------------

-- | Extract a raw rule from an AST
--
-- Note: This uses a dummy variable type since we only care about structure.
extractRule :: forall ts n steps.
               String  -- ^ Rule name
            -> IxFree (RuleF DummyRel ts) ('St 0 '[] 'False) ('St n steps 'True) ()
            -> RawRule
extractRule name ast =
  let finalState = runExtract ast emptyExtract
  in RawRule name (reverse $ esConclusion finalState) (reverse $ esPremises finalState)

-- | Dummy rel type for extraction (never executed)
data DummyRel a

-- | Run extraction, purely traversing the AST
runExtract :: IxFree (RuleF DummyRel ts) s t a -> ExtractState -> ExtractState
runExtract (Pure _) st = st
runExtract (Bind op k) st = case op of

  FreshF ->
    let varId = esNextVar st
        -- Create a placeholder term with the right variable ID
        term = T (error "typeset") (error "typeset")
        st' = st { esNextVar = varId + 1 }
    in runExtract (k term) st'

  ConclF applied ->
    let patterns = captureArgsTypeset (amArgs applied) (esNextVar st)
        st' = st { esConclusion = patterns }
    in runExtract (k ()) st'

  PremF applied ->
    let patterns = captureArgsTypeset (amArgs applied) 0  -- Start fresh for premises
        st' = st { esPremises = (amName applied, patterns) : esPremises st }
    in runExtract (k ()) st'

  NegF applied ->
    let patterns = captureArgsTypeset (amArgs applied) 0
        st' = st { esPremises = ("¬" ++ amName applied, patterns) : esPremises st }
    in runExtract (k ()) st'

  UnifyF _ _ ->
    -- Unification doesn't add visible premises in typesetting
    runExtract (k ()) st

  NeqF _ _ ->
    -- Same for disequality
    runExtract (k ()) st

  LiftRelF _ ->
    runExtract (k (error "typeset: LiftRelF")) st

  LiftRelDeferredF _ ->
    runExtract (k ()) st

-- | Capture argument list for typesetting
captureArgsTypeset :: LTermList rel ts -> Int -> [RawTerm]
captureArgsTypeset TNil _ = []
captureArgsTypeset (x :> xs) n =
  case capturePatternSimple n x of
    (term, n') -> term : captureArgsTypeset xs n'

-- | Simple pattern capture for LTerms
capturePatternSimple :: forall a rel. (LogicType a, Typeable a)
                     => Int -> Logic a (RVar rel) -> (RawTerm, Int)
capturePatternSimple n (Free _) = (RVar (VarRef n (typeRep (Proxy @a))), n + 1)
capturePatternSimple n (Ground r) =
  let (name, fields) = quote r
      (children, n') = captureFieldsSimple n fields
  in (RCon name children, n')

captureFieldsSimple :: Int -> [Field a (RVar rel)] -> ([RawTerm], Int)
captureFieldsSimple n [] = ([], n)
captureFieldsSimple n (Field (_ :: Proxy t) logic : rest) =
  let (term, n') = capturePatternSimple @t n logic
      (terms, n'') = captureFieldsSimple n' rest
  in (term : terms, n'')

-- | Extract rules from a list of ModedRules
extractRules :: [ModedRule DummyRel ts] -> [RawRule]
extractRules = map extractModedRule
  where
    extractModedRule :: ModedRule DummyRel ts -> RawRule
    extractModedRule (ModedRule name body) = extractRule name body

--------------------------------------------------------------------------------
-- Renumbering
--------------------------------------------------------------------------------

-- | Renumber variables: conclusion first, then premises
renumber :: RawRule -> DisplayRule
renumber raw =
  let conclVars = concatMap collectVars (rrConclusion raw)
      premVars = concatMap (concatMap collectVars . snd) (rrPremises raw)
      allVars = conclVars ++ premVars
      varMap = buildVarMap allVars
      newConclusion = map (applyVarMap varMap) (rrConclusion raw)
      newPremises = map (\(n, ts) -> (n, map (applyVarMap varMap) ts)) (rrPremises raw)
  in DisplayRule (rrName raw) newConclusion newPremises

-- | Collect all VarRefs in order
collectVars :: RawTerm -> [VarRef]
collectVars (RVar v) = [v]
collectVars (RCon _ children) = concatMap collectVars children

-- | Build mapping from VarRef to display number (per-type)
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

-- | Apply mapping to convert RawTerm to DisplayTerm
applyVarMap :: M.Map VarRef Int -> RawTerm -> DisplayTerm
applyVarMap m (RVar v) =
  let displayNum = M.findWithDefault 0 v m
  in DVar (DisplayVar displayNum (vrTypeRep v))
applyVarMap m (RCon name children) =
  DCon name (map (applyVarMap m) children)

--------------------------------------------------------------------------------
-- Formatting
--------------------------------------------------------------------------------

-- | Default variable names by type
defaultVarNames :: TypeRep -> [String]
defaultVarNames _ = map (\n -> "x" ++ subscriptNum n) [0..]

-- | Format a subscript number
subscriptNum :: Int -> String
subscriptNum n = map toSubscript (show n)
  where
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

-- | Format a display variable
formatVar :: DisplayVar -> String
formatVar (DisplayVar n tyRep) =
  let names = defaultVarNames tyRep
  in names !! n

-- | Format a display term
formatDisplayTerm :: DisplayTerm -> String
formatDisplayTerm (DVar dv) = formatVar dv
formatDisplayTerm (DCon name []) = name
formatDisplayTerm (DCon name args) =
  name ++ "(" ++ intercalate ", " (map formatDisplayTerm args) ++ ")"

-- | Intercalate strings
intercalate :: String -> [String] -> String
intercalate _ [] = ""
intercalate _ [x] = x
intercalate sep (x:xs) = x ++ sep ++ intercalate sep xs

-- | Format a display rule as ASCII inference rule
formatRule :: String -> DisplayRule -> String
formatRule judgmentName rule =
  let conclStr = formatJudgment judgmentName (map formatDisplayTerm (drConclusion rule))
      premStrs = map (\(pname, pargs) -> formatJudgment pname (map formatDisplayTerm pargs))
                     (drPremises rule)
      maxLen = maximum $ length conclStr : map length premStrs
      line = replicate (maxLen + 4) '─'
  in (if null premStrs then "" else unlines (map ("  " ++) premStrs)) ++
     "  " ++ line ++ " [" ++ drName rule ++ "]\n" ++
     "  " ++ conclStr

-- | Format a judgment (default implementation)
formatJudgment :: String -> [String] -> String
formatJudgment name [] = name
formatJudgment name args = name ++ "(" ++ intercalate ", " args ++ ")"
