{-# LANGUAGE QualifiedDo #-}

-- | User-facing DSL for defining typed inference rules
--
-- = Usage
--
-- @
-- {-# LANGUAGE QualifiedDo, DataKinds, TypeApplications #-}
-- import qualified TypedRedex.DSL as R
--
-- synth :: Judgment3 "synth" '[I, I, O] Ctx Tm Ty
-- synth = judgment3 $ \\rule ->
--   [ rule "=>Var" $ R.do
--       (ctx, x, ty) <- R.fresh3
--       R.concl $ synth ctx (var x) ty
--       R.prem  $ lookupCtx ctx x ty
--   ]
-- @
module TypedRedex.DSL
  ( -- * QualifiedDo
    return, (>>=), (>>)
  -- * Fresh variables
  , fresh, fresh2, fresh3, fresh4, fresh5
  -- * Rule operations
  , concl, prem, neg
  , (===), (=/=)
  -- * Rule construction
  , rule
  -- * Judgment types (function aliases)
  , Judgment1, Judgment2, Judgment3, Judgment4, Judgment5
  -- * Judgment constructors
  , judgment1, judgment2, judgment3, judgment4, judgment5
  -- * Re-exports
  , module TypedRedex.Core.Term
  , module TypedRedex.Core.RuleF
  ) where

import Prelude hiding (return, (>>=), (>>))
import Data.Proxy (Proxy(..))
import Data.Typeable (Typeable)
import GHC.TypeLits (Symbol, KnownSymbol, symbolVal, type (+))

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
-- Fresh variables
--------------------------------------------------------------------------------

fresh :: forall a ts n steps c. (Repr a, Typeable a)
      => RuleM ts ('St n steps c) ('St (n + 1) steps c) (Term '[n] a)
fresh = liftF FreshF

fresh2 :: forall a b ts n steps c.
          (Repr a, Typeable a, Repr b, Typeable b)
       => RuleM ts ('St n steps c) ('St (n + 2) steps c) (Term '[n] a, Term '[n + 1] b)
fresh2 = liftF Fresh2F

fresh3 :: forall a b c ts n steps cc.
          (Repr a, Typeable a, Repr b, Typeable b, Repr c, Typeable c)
       => RuleM ts ('St n steps cc) ('St (n + 3) steps cc)
            (Term '[n] a, Term '[n + 1] b, Term '[n + 2] c)
fresh3 = liftF Fresh3F

fresh4 :: forall a b c d ts n steps cc.
          (Repr a, Typeable a, Repr b, Typeable b, Repr c, Typeable c, Repr d, Typeable d)
       => RuleM ts ('St n steps cc) ('St (n + 4) steps cc)
            (Term '[n] a, Term '[n + 1] b, Term '[n + 2] c, Term '[n + 3] d)
fresh4 = liftF Fresh4F

fresh5 :: forall a b c d e ts n steps cc.
          (Repr a, Typeable a, Repr b, Typeable b, Repr c, Typeable c,
           Repr d, Typeable d, Repr e, Typeable e)
       => RuleM ts ('St n steps cc) ('St (n + 5) steps cc)
            (Term '[n] a, Term '[n + 1] b, Term '[n + 2] c, Term '[n + 3] d, Term '[n + 4] e)
fresh5 = liftF Fresh5F

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

neg :: forall ts ts' n steps c.
       Rule ts'
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
-- Rule construction
--------------------------------------------------------------------------------

rule :: forall name n steps ts.
        CheckSchedule name steps
     => String
     -> RuleM ts ('St 0 '[] 'False) ('St n steps 'True) ()
     -> Rule ts
rule = Rule

--------------------------------------------------------------------------------
-- Judgment types (functions returning JudgmentCall)
--------------------------------------------------------------------------------

type Judgment1 (name :: Symbol) (modes :: [Mode]) t1 =
  forall vs1. (InputVars modes '[vs1] '[t1], OutputVars modes '[vs1] '[t1])
  => Term vs1 t1 -> JudgmentCall name modes '[vs1] '[t1]

type Judgment2 (name :: Symbol) (modes :: [Mode]) t1 t2 =
  forall vs1 vs2. (InputVars modes '[vs1, vs2] '[t1, t2], OutputVars modes '[vs1, vs2] '[t1, t2])
  => Term vs1 t1 -> Term vs2 t2 -> JudgmentCall name modes '[vs1, vs2] '[t1, t2]

type Judgment3 (name :: Symbol) (modes :: [Mode]) t1 t2 t3 =
  forall vs1 vs2 vs3.
    (InputVars modes '[vs1, vs2, vs3] '[t1, t2, t3], OutputVars modes '[vs1, vs2, vs3] '[t1, t2, t3])
  => Term vs1 t1 -> Term vs2 t2 -> Term vs3 t3
  -> JudgmentCall name modes '[vs1, vs2, vs3] '[t1, t2, t3]

type Judgment4 (name :: Symbol) (modes :: [Mode]) t1 t2 t3 t4 =
  forall vs1 vs2 vs3 vs4.
    (InputVars modes '[vs1, vs2, vs3, vs4] '[t1, t2, t3, t4],
     OutputVars modes '[vs1, vs2, vs3, vs4] '[t1, t2, t3, t4])
  => Term vs1 t1 -> Term vs2 t2 -> Term vs3 t3 -> Term vs4 t4
  -> JudgmentCall name modes '[vs1, vs2, vs3, vs4] '[t1, t2, t3, t4]

type Judgment5 (name :: Symbol) (modes :: [Mode]) t1 t2 t3 t4 t5 =
  forall vs1 vs2 vs3 vs4 vs5.
    (InputVars modes '[vs1, vs2, vs3, vs4, vs5] '[t1, t2, t3, t4, t5],
     OutputVars modes '[vs1, vs2, vs3, vs4, vs5] '[t1, t2, t3, t4, t5])
  => Term vs1 t1 -> Term vs2 t2 -> Term vs3 t3 -> Term vs4 t4 -> Term vs5 t5
  -> JudgmentCall name modes '[vs1, vs2, vs3, vs4, vs5] '[t1, t2, t3, t4, t5]

--------------------------------------------------------------------------------
-- Judgment constructors
--------------------------------------------------------------------------------

-- | Construct a 1-argument judgment
-- Note: Schedule checking happens at rule construction time, not judgment definition
judgment1
  :: forall name modes t1.
     (KnownSymbol name, SingModeList modes, Repr t1, Typeable t1)
  => [Rule '[t1]]
  -> Judgment1 name modes t1
judgment1 rules t1 = JudgmentCall
  { jcName     = symbolVal (Proxy @name)
  , jcModes    = singModeList
  , jcArgs     = t1 :> TNil
  , jcReqVars  = inputVars (singModeList @modes) (t1 :> TNil)
  , jcProdVars = outputVars (singModeList @modes) (t1 :> TNil)
  , jcRules    = rules
  }

-- | Construct a 2-argument judgment
judgment2
  :: forall name modes t1 t2.
     (KnownSymbol name, SingModeList modes, Repr t1, Typeable t1, Repr t2, Typeable t2)
  => [Rule '[t1, t2]]
  -> Judgment2 name modes t1 t2
judgment2 rules t1 t2 = JudgmentCall
  { jcName     = symbolVal (Proxy @name)
  , jcModes    = singModeList
  , jcArgs     = t1 :> t2 :> TNil
  , jcReqVars  = inputVars (singModeList @modes) (t1 :> t2 :> TNil)
  , jcProdVars = outputVars (singModeList @modes) (t1 :> t2 :> TNil)
  , jcRules    = rules
  }

-- | Construct a 3-argument judgment
judgment3
  :: forall name modes t1 t2 t3.
     (KnownSymbol name, SingModeList modes,
      Repr t1, Typeable t1, Repr t2, Typeable t2, Repr t3, Typeable t3)
  => [Rule '[t1, t2, t3]]
  -> Judgment3 name modes t1 t2 t3
judgment3 rules t1 t2 t3 = JudgmentCall
  { jcName     = symbolVal (Proxy @name)
  , jcModes    = singModeList
  , jcArgs     = t1 :> t2 :> t3 :> TNil
  , jcReqVars  = inputVars (singModeList @modes) (t1 :> t2 :> t3 :> TNil)
  , jcProdVars = outputVars (singModeList @modes) (t1 :> t2 :> t3 :> TNil)
  , jcRules    = rules
  }

-- | Construct a 4-argument judgment
judgment4
  :: forall name modes t1 t2 t3 t4.
     (KnownSymbol name, SingModeList modes,
      Repr t1, Typeable t1, Repr t2, Typeable t2, Repr t3, Typeable t3, Repr t4, Typeable t4)
  => [Rule '[t1, t2, t3, t4]]
  -> Judgment4 name modes t1 t2 t3 t4
judgment4 rules t1 t2 t3 t4 = JudgmentCall
  { jcName     = symbolVal (Proxy @name)
  , jcModes    = singModeList
  , jcArgs     = t1 :> t2 :> t3 :> t4 :> TNil
  , jcReqVars  = inputVars (singModeList @modes) (t1 :> t2 :> t3 :> t4 :> TNil)
  , jcProdVars = outputVars (singModeList @modes) (t1 :> t2 :> t3 :> t4 :> TNil)
  , jcRules    = rules
  }

-- | Construct a 5-argument judgment
judgment5
  :: forall name modes t1 t2 t3 t4 t5.
     (KnownSymbol name, SingModeList modes,
      Repr t1, Typeable t1, Repr t2, Typeable t2, Repr t3, Typeable t3,
      Repr t4, Typeable t4, Repr t5, Typeable t5)
  => [Rule '[t1, t2, t3, t4, t5]]
  -> Judgment5 name modes t1 t2 t3 t4 t5
judgment5 rules t1 t2 t3 t4 t5 = JudgmentCall
  { jcName     = symbolVal (Proxy @name)
  , jcModes    = singModeList
  , jcArgs     = t1 :> t2 :> t3 :> t4 :> t5 :> TNil
  , jcReqVars  = inputVars (singModeList @modes) (t1 :> t2 :> t3 :> t4 :> t5 :> TNil)
  , jcProdVars = outputVars (singModeList @modes) (t1 :> t2 :> t3 :> t4 :> t5 :> TNil)
  , jcRules    = rules
  }
