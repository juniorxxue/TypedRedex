{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes #-}

-- | User-facing DSL for defining typed inference rules
--
-- = Usage
--
-- @
-- {-# LANGUAGE QualifiedDo, DataKinds #-}
-- import qualified TypedRedex.DSL as R
--
-- add :: Judgment "add" '[I, I, O] '[Nat, Nat, Nat]
-- add = judgment
--   [ rule "add-zero" $ R.do
--       y <- R.fresh
--       R.concl $ add zro y y
--   , rule "add-succ" $ R.do
--       x <- R.fresh
--       y <- R.fresh
--       z <- R.fresh
--       R.concl $ add (suc x) y (suc z)
--       R.prem  $ add x y z
--   ]
-- @
--
module TypedRedex.DSL
  ( -- * QualifiedDo
    return, (>>=), (>>)
    -- * Fresh variables
  , fresh
  , Fresh
    -- * Rule operations
  , concl, prem, neg
  , (===), (=/=)
    -- * Judgments
  , rule
  , rules
  , Judgment
  , judgment
  , judgmentWith
  , format
  , RuleBuilder
  , JudgmentBuilder
    -- * Re-exports
  , module TypedRedex.Core.Term
  , module TypedRedex.Core.RuleF
  ) where

import Prelude hiding (return, (>>=), (>>))
import Control.Monad.State.Strict (State, get, put, runState)
import Data.Proxy (Proxy(..))
import Data.Typeable (Typeable)
import GHC.TypeLits (Symbol, KnownSymbol, symbolVal)
import Data.Kind (Type)
import GHC.Generics (Generic, Rep, U1(..), (:*:)(..), M1(..), K1(..), to)

import TypedRedex.Core.IxFree (liftF)
import qualified TypedRedex.Core.IxFree as Ix
import TypedRedex.Core.Term
import TypedRedex.Core.RuleF
import TypedRedex.Pretty (Doc, FmtFn(..), FmtArgs)

--------------------------------------------------------------------------------
-- QualifiedDo
--------------------------------------------------------------------------------

return :: a -> RuleM ts a
return = Ix.return

(>>=) :: RuleM ts a -> (a -> RuleM ts b) -> RuleM ts b
(>>=) = (Ix.>>=)

(>>) :: RuleM ts a -> RuleM ts b -> RuleM ts b
(>>) = (Ix.>>)

--------------------------------------------------------------------------------
-- Fresh variables
--------------------------------------------------------------------------------

-- | Allocate fresh logic variables.
--
-- Supports tuples and other product types via Generics.
class Fresh t where
  fresh :: RuleM ts t

instance {-# OVERLAPPING #-} (Repr a, Typeable a) => Fresh (Term a) where
  fresh = liftF FreshF

instance {-# OVERLAPPABLE #-} (Generic t, GFresh (Rep t)) => Fresh t where
  fresh = gFresh >>= (return . to)

class GFresh f where
  gFresh :: RuleM ts (f p)

instance GFresh U1 where
  gFresh = return U1

instance (GFresh a, GFresh b) => GFresh (a :*: b) where
  gFresh =
    gFresh >>= \a ->
      gFresh >>= \b ->
        return (a :*: b)

instance GFresh a => GFresh (M1 i c a) where
  gFresh = gFresh >>= \a -> return (M1 a)

instance Fresh a => GFresh (K1 i a) where
  gFresh = fresh >>= \a -> return (K1 a)

--------------------------------------------------------------------------------
-- Rule operations
--------------------------------------------------------------------------------

concl :: JudgmentCall name modes ts -> RuleM ts ()
concl = liftF . ConclF

prem :: JudgmentCall name modes ts' -> RuleM ts ()
prem = liftF . PremF

neg :: Rule name ts' -> RuleM ts ()
neg = liftF . NegF

infix 4 ===, =/=

(===) :: forall a ts. (Repr a, Typeable a)
      => Term a -> Term a
      -> RuleM ts ()
(===) t1 t2 = liftF (EqF t1 t2)

(=/=) :: forall a ts. (Repr a, Typeable a)
      => Term a -> Term a
      -> RuleM ts ()
(=/=) t1 t2 = liftF (NEqF t1 t2)

--------------------------------------------------------------------------------
-- Constructing judgments
--------------------------------------------------------------------------------

-- | Type alias for the rule builder function
type RuleBuilder (name :: Symbol) ts =
  String
  -> RuleM ts ()
  -> Rule name ts

-- | Define a rule with compile-time schedule checking.
rule :: forall name ts. String -> RuleM ts () -> Rule name ts
rule = Rule

--------------------------------------------------------------------------------
-- Judgment builder
--------------------------------------------------------------------------------

data JBState name modes ts = JBState
  { jbRules  :: [Rule name ts]
  , jbFormat :: Maybe ([Doc] -> Doc)
  }

newtype JudgmentBuilder name modes ts a = JudgmentBuilder (State (JBState name modes ts) a)
  deriving (Functor, Applicative, Monad)

runJudgmentBuilder :: JudgmentBuilder name modes ts a -> (Maybe ([Doc] -> Doc), [Rule name ts])
runJudgmentBuilder (JudgmentBuilder st) =
  let initState = JBState [] Nothing
      ((), endState) = runState (void st) initState
  in (jbFormat endState, jbRules endState)
  where
    void :: Functor f => f a -> f ()
    void = fmap (const ())

addRule :: Rule name ts -> JudgmentBuilder name modes ts ()
addRule r = JudgmentBuilder $ do
  s <- get
  put s { jbRules = jbRules s ++ [r] }

rules :: [Rule name ts] -> JudgmentBuilder name modes ts ()
rules = mapM_ addRule

-- | Specify a custom formatter for judgment conclusions.
-- Omit this to use the default prefix formatter.
format :: forall name modes ts f.
          FmtFn (FmtArgs ts) f
       => f
       -> JudgmentBuilder name modes ts ()
format f = JudgmentBuilder $ do
  s <- get
  put s { jbFormat = Just (toFmt @(FmtArgs ts) f) }


class JudgmentSpec spec (name :: Symbol) (ts :: [Type]) | spec -> name ts where
  buildJudgmentSpec :: spec -> (Maybe ([Doc] -> Doc), [Rule name ts])

instance JudgmentSpec [Rule name ts] name ts where
  buildJudgmentSpec rs = (Nothing, rs)

instance JudgmentSpec (JudgmentBuilder name modes ts a) name ts where
  buildJudgmentSpec = runJudgmentBuilder

-- | Define a judgment with the given rules.
--
-- Prefer using a type signature to fix the judgment name/modes, so you
-- don't need to repeat them with type applications.
judgment
  :: forall name modes ts spec.
     (KnownSymbol name, SingModeList modes, JudgmentSpec spec name ts, BuildArgs ts, PrettyList ts)
  => spec
  -> Judgment name modes ts
judgment spec =
  let (fmt, rules') = buildJudgmentSpec spec
      jd = JudgmentDef
        { judgmentName  = symbolVal (Proxy @name)
        , judgmentModes = singModeList @modes
        , judgmentRules = rules'
        , judgmentFormat = fmt
        }
  in applyJudgment jd

-- | Backwards-compatible helper for building judgments with a @rule@ callback.
judgmentWith
  :: forall name modes ts.
     (KnownSymbol name, SingModeList modes, BuildArgs ts, PrettyList ts)
  => (RuleBuilder name ts -> [Rule name ts])
  -> Judgment name modes ts
judgmentWith mkRules = judgment @name @modes @ts (mkRules Rule)

--------------------------------------------------------------------------------
-- Applying judgments
--------------------------------------------------------------------------------

type family CurriedArgs (ts :: [Type]) (r :: Type) :: Type where
  CurriedArgs '[] r = r
  CurriedArgs (a ': ts) r = Term a -> CurriedArgs ts r

-- | A judgment is a curried function from terms to a judgment call.
type Judgment name modes ts = CurriedArgs ts (JudgmentCall name modes ts)

class BuildArgs (ts :: [Type]) where
  buildArgs :: (TermList ts -> r) -> CurriedArgs ts r

instance BuildArgs '[] where
  buildArgs k = k TNil

instance (Repr a, Typeable a, BuildArgs ts) => BuildArgs (a ': ts) where
  buildArgs k = \a -> buildArgs (\tl -> k (a :> tl))

mkJudgmentCall
  :: forall name modes ts.
     PrettyList ts
  => JudgmentDef name modes ts
  -> TermList ts
  -> JudgmentCall name modes ts
mkJudgmentCall jd tl =
  let ms = judgmentModes jd
      req = inputVars ms tl
      prod = outputVars ms tl
  in JudgmentCall
       { jcName = judgmentName jd
       , jcModes = ms
       , jcArgs = tl
       , jcReqVars = req
       , jcProdVars = prod
       , jcRules = judgmentRules jd
       , jcFormat = judgmentFormat jd
       , jcPretty = prettyTermList tl
       }

applyJudgment
  :: forall name modes ts.
     (BuildArgs ts, PrettyList ts)
  => JudgmentDef name modes ts
  -> Judgment name modes ts
applyJudgment jd = buildArgs (mkJudgmentCall jd)
