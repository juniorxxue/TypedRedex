{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes #-}

-- | User-facing DSL for defining typed inference rules
--
-- = Usage
--
-- @
-- {-# LANGUAGE QualifiedDo, DataKinds, TypeApplications, ScopedTypeVariables #-}
-- import qualified TypedRedex.DSL as R
--
-- add :: Judgment "add" '[I, I, O] '[Nat, Nat, Nat]
-- add = judgment
--   [ rule "add-zero" $ R.do
--       y <- R.freshVar \@Nat
--       R.concl $ add # (zro, y, y)
--   , rule "add-succ" $ R.do
--       x <- R.freshVar \@Nat
--       y <- R.freshVar \@Nat
--       z <- R.freshVar \@Nat
--       R.concl $ add # (suc x, y, suc z)
--       R.prem  $ add # (x, y, z)
--   ]
-- @
--
-- NOTE: GHC sometimes needs help inferring the sort of fresh variables; prefer
-- `freshVar \@T` to avoid writing explicit @'[n]@ indices in user code.
module TypedRedex.DSL
  ( -- * QualifiedDo
    return, (>>=), (>>)
    -- * Fresh variables (generic)
  , Fresh(..)
  , freshVar
    -- * Rule operations
  , concl, prem, neg
  , (===), (=/=)
    -- * Judgments
  , rule
  , judgment
  , judgmentWith
  , (#)
  , RuleBuilder
    -- * Re-exports
  , module TypedRedex.Core.Term
  , module TypedRedex.Core.RuleF
  ) where

import Prelude hiding (return, (>>=), (>>))
import Data.Proxy (Proxy(..))
import Data.Typeable (Typeable)
import GHC.TypeLits (Symbol, KnownSymbol, symbolVal, type (+), Nat)
import GHC.Generics (Generic, Rep, to, K1(..), M1(..), U1(..), (:*:)(..))
import Data.Kind (Type)

import TypedRedex.Core.IxFree (liftF)
import qualified TypedRedex.Core.IxFree as Ix
import TypedRedex.Core.Term
import TypedRedex.Core.RuleF

--------------------------------------------------------------------------------
-- QualifiedDo
--------------------------------------------------------------------------------

return :: a -> RuleM ts s s a
return = Ix.return

(>>=) :: RuleM ts s t a -> (a -> RuleM ts t u b) -> RuleM ts s u b
(>>=) = (Ix.>>=)

(>>) :: RuleM ts s t a -> RuleM ts t u b -> RuleM ts s u b
(>>) = (Ix.>>)

--------------------------------------------------------------------------------
-- Fresh variables (generic via GHC.Generics)
--------------------------------------------------------------------------------

-- | Type family for counting fresh variables.
-- Single Term produces 1; tuples use GFreshCount via Generics.
type family FreshCount r :: Nat where
  FreshCount (Term vs a) = 1
  FreshCount r = GFreshCount (Rep r)

-- | Typeclass for allocating fresh logic variables.
-- Works for single Term values and tuples of Term values.
--
-- @
-- x <- fresh           -- single variable
-- (x, y) <- fresh      -- two variables
-- (x, y, z) <- fresh   -- three variables
-- @
class Fresh r ts n steps c where
  fresh :: RuleM ts ('St n steps c) ('St (n + FreshCount r) steps c) r

-- | Base case: single variable
instance (Repr a, Typeable a, vs ~ '[n]) => Fresh (Term vs a) ts n steps c where
  fresh = liftF FreshF

-- | Allocate a single fresh variable of a given sort.
--
-- This is a convenience for avoiding explicit @'[n]@ annotations:
--
-- @
-- x <- freshVar \@Nat
-- y <- freshVar \@Nat
-- @
freshVar
  :: forall a ts n steps c.
     (Repr a, Typeable a)
  => RuleM ts ('St n steps c) ('St (n + 1) steps c) (Term '[n] a)
freshVar = liftF FreshF

-- | Generic case: tuples and other product types
instance {-# OVERLAPPABLE #-}
  ( Generic r, GFresh (Rep r) ts n steps c
  , FreshCount r ~ GFreshCount (Rep r)
  ) => Fresh r ts n steps c where
  fresh = gfresh >>= \rep -> return (to rep)

--------------------------------------------------------------------------------
-- GFresh (Generic traversal for fresh allocation)
--------------------------------------------------------------------------------

-- | Closed type family for counting fresh variables in generic representation.
type family GFreshCount (f :: Type -> Type) :: Nat where
  GFreshCount U1 = 0
  GFreshCount (M1 i m f) = GFreshCount f
  GFreshCount (f :*: g) = GFreshCount f + GFreshCount g
  GFreshCount (K1 i (Term vs a)) = 1

-- | Generic fresh variable allocation for product types
class GFresh (f :: Type -> Type) ts n steps c where
  gfresh :: RuleM ts ('St n steps c) ('St (n + GFreshCount f) steps c) (f p)

-- | Unit (empty product)
instance GFresh U1 ts n steps c where
  gfresh = return U1

-- | Metadata wrapper (pass through)
instance GFresh f ts n steps c => GFresh (M1 i m f) ts n steps c where
  gfresh = gfresh >>= \x -> return (M1 x)

-- | Product: process left then right, threading state
instance forall f g ts n steps c.
  ( GFresh f ts n steps c
  , GFresh g ts (n + GFreshCount f) steps c
  ) => GFresh (f :*: g) ts n steps c where
  gfresh =
    gfresh @f @ts @n @steps @c >>= \a ->
    gfresh @g @ts @(n + GFreshCount f) @steps @c >>= \b ->
    return (a :*: b)

-- | Leaf: single Term value
instance (Repr a, Typeable a, vs ~ '[n]) => GFresh (K1 i (Term vs a)) ts n steps c where
  gfresh = liftF FreshF >>= \t -> return (K1 t)

--------------------------------------------------------------------------------
-- Rule operations
--------------------------------------------------------------------------------

concl :: forall name modes vss ts n steps.
         (InputVars modes vss ts, OutputVars modes vss ts)
      => JudgmentCall name modes vss ts
      -> RuleM ts ('St n steps 'False)
                  ('St n (Snoc steps ('ConcStep name (ReqVars modes vss) (ProdVars modes vss))) 'True) ()
concl = liftF . ConclF

prem :: forall name modes vss ts ts' n steps c.
        (InputVars modes vss ts', OutputVars modes vss ts')
     => JudgmentCall name modes vss ts'
     -> RuleM ts ('St n steps c)
                 ('St n (Snoc steps ('PremStep ('Goal name (ReqVars modes vss) (ProdVars modes vss)))) c) ()
prem = liftF . PremF

neg :: forall name ts ts' n steps c.
       Rule name ts'
    -> RuleM ts ('St n steps c) ('St n (Snoc steps ('NegStep '[])) c) ()
neg = liftF . NegF

infix 4 ===, =/=

(===) :: forall a ts vs1 vs2 n steps c. (Repr a, Typeable a)
      => Term vs1 a -> Term vs2 a
      -> RuleM ts ('St n steps c)
                  ('St n (Snoc steps ('PremStep ('Goal "==" (Union vs1 vs2) '[]))) c) ()
(===) t1 t2 = liftF (EqF t1 t2)

(=/=) :: forall a ts vs1 vs2 n steps c. (Repr a, Typeable a)
      => Term vs1 a -> Term vs2 a
      -> RuleM ts ('St n steps c)
                  ('St n (Snoc steps ('PremStep ('Goal "=/=" (Union vs1 vs2) '[]))) c) ()
(=/=) t1 t2 = liftF (NEqF t1 t2)

--------------------------------------------------------------------------------
-- Constructing judgments
--------------------------------------------------------------------------------

-- | Type alias for the rule builder function
type RuleBuilder (name :: Symbol) ts =
  forall n steps. CheckSchedule name steps
  => String
  -> RuleM ts ('St 0 '[] 'False) ('St n steps 'True) ()
  -> Rule name ts

-- | Define a rule with compile-time schedule checking.
rule
  :: forall name ts n steps.
     CheckSchedule name steps
  => String
  -> RuleM ts ('St 0 '[] 'False) ('St n steps 'True) ()
  -> Rule name ts
rule = Rule

-- | Define a judgment with the given rules.
--
-- Prefer using a type signature to fix the judgment name/modes, so you
-- don't need to repeat them with type applications.
judgment
  :: forall name modes ts.
     (KnownSymbol name, SingModeList modes)
  => [Rule name ts]
  -> Judgment name modes ts
judgment rules = Judgment
  { judgmentName  = symbolVal (Proxy @name)
  , judgmentModes = singModeList @modes
  , judgmentRules = rules
  }

-- | Backwards-compatible helper for building judgments with a @rule@ callback.
judgmentWith
  :: forall name modes ts.
     (KnownSymbol name, SingModeList modes)
  => (RuleBuilder name ts -> [Rule name ts])
  -> Judgment name modes ts
judgmentWith mkRules = judgment (mkRules rule)

--------------------------------------------------------------------------------
-- Applying judgments
--------------------------------------------------------------------------------

class ToTermList args vss ts | args -> vss ts where
  toTermList :: args -> TermList vss ts

instance ToTermList (TermList vss ts) vss ts where
  toTermList = id

instance (Repr a, Typeable a) => ToTermList (Term vs a) '[vs] '[a] where
  toTermList t = t :> TNil

instance (Repr a, Typeable a, Repr b, Typeable b) => ToTermList (Term vs1 a, Term vs2 b) '[vs1, vs2] '[a, b] where
  toTermList (a, b) = a :> b :> TNil

instance (Repr a, Typeable a, Repr b, Typeable b, Repr c, Typeable c)
  => ToTermList (Term vs1 a, Term vs2 b, Term vs3 c) '[vs1, vs2, vs3] '[a, b, c] where
  toTermList (a, b, c) = a :> b :> c :> TNil

instance (Repr a, Typeable a, Repr b, Typeable b, Repr c, Typeable c, Repr d, Typeable d)
  => ToTermList (Term vs1 a, Term vs2 b, Term vs3 c, Term vs4 d) '[vs1, vs2, vs3, vs4] '[a, b, c, d] where
  toTermList (a, b, c, d) = a :> b :> c :> d :> TNil

instance (Repr a, Typeable a, Repr b, Typeable b, Repr c, Typeable c, Repr d, Typeable d, Repr e, Typeable e)
  => ToTermList (Term vs1 a, Term vs2 b, Term vs3 c, Term vs4 d, Term vs5 e) '[vs1, vs2, vs3, vs4, vs5] '[a, b, c, d, e] where
  toTermList (a, b, c, d, e) = a :> b :> c :> d :> e :> TNil

infixl 1 #

-- | Apply a judgment to arguments, creating a judgment call.
(#)
  :: forall name modes ts args vss.
     ( ToTermList args vss ts
     , InputVars modes vss ts
     , OutputVars modes vss ts
     )
  => Judgment name modes ts
  -> args
  -> JudgmentCall name modes vss ts
(#) j args =
  let tl = toTermList args
      ms = judgmentModes j
      req = inputVars ms tl
      prod = outputVars ms tl
  in JudgmentCall
       { jcName = judgmentName j
       , jcModes = ms
       , jcArgs = tl
       , jcReqVars = req
       , jcProdVars = prod
       , jcRules = judgmentRules j
       }
