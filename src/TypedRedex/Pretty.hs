{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Pretty-printing utilities for terms and judgments.
--
-- This module provides a small Doc type, variable naming helpers, and
-- a Pretty class for formatting logic terms. The design is opt-in:
-- if no Pretty instance is provided, a generic prefix formatter is used.
module TypedRedex.Pretty
  ( -- * Doc
    Doc(..)
  , text
  , (<+>)
  , parens
  , brackets
  , braces
  , commaSep
  , spaceSep
    -- * Naming
  , VarNames
  , cycleNames
  , numberedNames
    -- * Pretty class
  , Pretty(..)
  , PrettyCtx
  , PrettyM
  , runPretty
  , runPrettyWith
  , emptyPrettyCtx
  , maskedPrettyCtx
  , prettyLogic
  , prettyTerm
  , prettyGround
    -- * Pretty term wrapper
  , PrettyTerm(..)
  , prettyTermDoc
    -- * Judgment formatting helpers
  , defaultJudgment
  , formatJudgment
    -- * Format arity
  , FmtArgs
  , FmtFn(..)
  ) where

import Data.Kind (Type)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.String (IsString(..))
import Data.Typeable (TypeRep, typeRep)
import Control.Monad.State.Strict (State, get, put, runState)
import Data.Proxy (Proxy(..))

import TypedRedex.Core.Term

--------------------------------------------------------------------------------
-- Doc
--------------------------------------------------------------------------------

newtype Doc = Doc { renderDoc :: String }
  deriving (Eq, Show)

instance IsString Doc where
  fromString = Doc

instance Semigroup Doc where
  Doc a <> Doc b = Doc (a ++ b)

instance Monoid Doc where
  mempty = Doc ""

text :: String -> Doc
text = Doc

infixr 6 <+>
-- | Concatenate Docs (avoids ambiguity with OverloadedStrings).
(<+>) :: Doc -> Doc -> Doc
(<+>) = (<>)

parens :: Doc -> Doc
parens d = Doc "(" <> d <> Doc ")"

brackets :: Doc -> Doc
brackets d = Doc "[" <> d <> Doc "]"

braces :: Doc -> Doc
braces d = Doc "{" <> d <> Doc "}"

commaSep :: [Doc] -> Doc
commaSep [] = mempty
commaSep [d] = d
commaSep (d:ds) = d <> Doc ", " <> commaSep ds

spaceSep :: [Doc] -> Doc
spaceSep [] = mempty
spaceSep [d] = d
spaceSep (d:ds) = d <> Doc " " <> spaceSep ds

--------------------------------------------------------------------------------
-- Naming helpers
--------------------------------------------------------------------------------

type VarNames = [String]

-- | A, B, C, A1, B1, C1, ...
cycleNames :: [String] -> VarNames
cycleNames [] = numberedNames "?"
cycleNames bases =
  [ base ++ suffix i
  | i <- [0 :: Int ..]
  , base <- bases
  ]
  where
    suffix 0 = ""
    suffix n = show n

-- | x, x1, x2, ...
numberedNames :: String -> VarNames
numberedNames sym = sym : [sym ++ show i | i <- [1 :: Int ..]]

--------------------------------------------------------------------------------
-- Pretty class
--------------------------------------------------------------------------------

data VarStyle
  = VarStyleNamed   -- ^ Use each type's 'varNames' to name logic variables.
  | VarStyleMasked  -- ^ Render all logic variables as "?" (hides unification ids).

data PrettyCtx = PrettyCtx
  { pcVarMap :: Map (TypeRep, Int) Int
  , pcNext   :: Map TypeRep Int
  , pcVarStyle :: VarStyle
  }

emptyPrettyCtx :: PrettyCtx
emptyPrettyCtx = PrettyCtx M.empty M.empty VarStyleNamed

-- | Pretty-print context that hides all logic variables as "?".
--
-- Useful for interactive debug output where exposing unification variable
-- identities is distracting.
maskedPrettyCtx :: PrettyCtx
maskedPrettyCtx = emptyPrettyCtx { pcVarStyle = VarStyleMasked }

newtype PrettyM a = PrettyM (State PrettyCtx a)
  deriving (Functor, Applicative, Monad)

runPrettyWith :: PrettyCtx -> PrettyM a -> (a, PrettyCtx)
runPrettyWith ctx (PrettyM st) = runState st ctx

runPretty :: PrettyM a -> a
runPretty = fst . runPrettyWith emptyPrettyCtx

class Repr a => Pretty a where
  -- | Infinite list of variable names for this type.
  varNames :: VarNames
  varNames = numberedNames "?"

  -- | Pretty-print a ground reified value.
  prettyReified :: Reified a -> PrettyM Doc
  prettyReified r = defaultPrettyReified r

-- | Default pretty instance: prefix formatting with numbered variables.
instance {-# OVERLAPPABLE #-} Repr a => Pretty a where
  prettyReified r = do
    let (name, fields) = quote r
    docs <- mapM prettyField fields
    pure (defaultCon name docs)
    where
      prettyField :: Field -> PrettyM Doc
      prettyField (Field l) = prettyLogic l

prettyVar :: forall a. Pretty a => Int -> PrettyM Doc
prettyVar vid = PrettyM $ do
  st <- get
  case pcVarStyle st of
    VarStyleMasked ->
      pure (Doc "?")
    VarStyleNamed -> do
      let ty = typeRep (Proxy @a)
      case M.lookup (ty, vid) (pcVarMap st) of
        Just idx -> pure (Doc (varNames @a !! idx))
        Nothing -> do
          let nextIdx = M.findWithDefault 0 ty (pcNext st)
              name = varNames @a !! nextIdx
              st' = st
                { pcVarMap = M.insert (ty, vid) nextIdx (pcVarMap st)
                , pcNext = M.insert ty (nextIdx + 1) (pcNext st)
                }
          put st'
          pure (Doc name)

prettyLogic :: forall a. Pretty a => Logic a -> PrettyM Doc
prettyLogic (Var i) = prettyVar @a i
prettyLogic (Ground r) = prettyReified r

prettyTerm :: forall a. Pretty a => Term a -> PrettyM Doc
prettyTerm (Term _ l) = prettyLogic l

prettyGround :: forall a. Pretty a => a -> Doc
prettyGround x = runPretty (prettyReified (project x))

--------------------------------------------------------------------------------
-- Pretty term wrapper
--------------------------------------------------------------------------------

data PrettyTerm where
  PrettyTerm :: Pretty a => Logic a -> PrettyTerm

prettyTermDoc :: PrettyTerm -> PrettyM Doc
prettyTermDoc (PrettyTerm l) = prettyLogic l

--------------------------------------------------------------------------------
-- Judgment formatting
--------------------------------------------------------------------------------

defaultJudgment :: String -> [Doc] -> Doc
defaultJudgment name [] = Doc name
defaultJudgment name args = Doc name <> Doc "(" <> commaSep args <> Doc ")"

formatJudgment :: String -> Maybe ([Doc] -> Doc) -> [Doc] -> Doc
formatJudgment name fmt args =
  case fmt of
    Just f  -> f args
    Nothing -> defaultJudgment name args

--------------------------------------------------------------------------------
-- Format arity
--------------------------------------------------------------------------------

type family FmtArgs (ts :: [Type]) :: [Type] where
  FmtArgs '[] = '[]
  FmtArgs (_ ': xs) = Doc ': FmtArgs xs

class FmtFn (args :: [Type]) f where
  toFmt :: f -> [Doc] -> Doc

instance FmtFn '[] Doc where
  toFmt d _ = d

instance FmtFn args f => FmtFn (Doc ': args) (Doc -> f) where
  toFmt f (a:rest) = toFmt @args (f a) rest
  toFmt _ [] = error "format: arity mismatch"

instance FmtFn '[Doc, Doc] ((Doc, Doc) -> Doc) where
  toFmt f [a, b] = f (a, b)
  toFmt _ _ = error "format: arity mismatch"

instance FmtFn '[Doc, Doc, Doc] ((Doc, Doc, Doc) -> Doc) where
  toFmt f [a, b, c] = f (a, b, c)
  toFmt _ _ = error "format: arity mismatch"

instance FmtFn '[Doc, Doc, Doc, Doc] ((Doc, Doc, Doc, Doc) -> Doc) where
  toFmt f [a, b, c, d] = f (a, b, c, d)
  toFmt _ _ = error "format: arity mismatch"

instance FmtFn '[Doc, Doc, Doc, Doc, Doc] ((Doc, Doc, Doc, Doc, Doc) -> Doc) where
  toFmt f [a, b, c, d, e] = f (a, b, c, d, e)
  toFmt _ _ = error "format: arity mismatch"

instance FmtFn '[Doc, Doc, Doc, Doc, Doc, Doc] ((Doc, Doc, Doc, Doc, Doc, Doc) -> Doc) where
  toFmt f [a, b, c, d, e, g] = f (a, b, c, d, e, g)
  toFmt _ _ = error "format: arity mismatch"

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

defaultCon :: String -> [Doc] -> Doc
defaultCon name [] = Doc name
defaultCon name args = Doc name <> Doc "(" <> commaSep args <> Doc ")"

defaultPrettyReified :: Repr a => Reified a -> PrettyM Doc
defaultPrettyReified r = do
  let (name, fields) = quote r
  docs <- mapM prettyField fields
  pure (defaultCon name docs)
  where
    prettyField :: Field -> PrettyM Doc
    prettyField (Field l) = prettyLogic l
