{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PolyKinds #-}

-- | Simple typesetting API for inference rules.
--
-- Usage:
--
-- @
-- typeset2 flipPolar
-- typeset3 lookupTmVar
-- typeset5 ssub
-- @
module Typeset
  ( typeset2
  , typeset3
  , typeset4
  , typeset5
  , typeset6
  ) where

import TypedRedex.Interp.Typesetting (TypesettingRedex, printRules, modedVar)
import TypedRedex.DSL.Moded (toApplied, T, AppliedM)
import TypedRedex.DSL.Define (Applied(..))
import TypedRedex.Logic (LogicType)

--------------------------------------------------------------------------------
-- Typeset functions (one per arity)
--------------------------------------------------------------------------------

-- | Typeset a 2-argument judgment.
typeset2 :: forall name modes t1 t2.
            (LogicType t1, LogicType t2)
         => (T '[] t1 TypesettingRedex -> T '[] t2 TypesettingRedex
             -> AppliedM TypesettingRedex name modes '[ '[], '[] ] '[t1, t2])
         -> IO ()
typeset2 j = printRules $ appGoal $ toApplied $ j (modedVar 0) (modedVar 1)

-- | Typeset a 3-argument judgment.
typeset3 :: forall name modes t1 t2 t3.
            (LogicType t1, LogicType t2, LogicType t3)
         => (T '[] t1 TypesettingRedex -> T '[] t2 TypesettingRedex -> T '[] t3 TypesettingRedex
             -> AppliedM TypesettingRedex name modes '[ '[], '[], '[] ] '[t1, t2, t3])
         -> IO ()
typeset3 j = printRules $ appGoal $ toApplied $ j (modedVar 0) (modedVar 1) (modedVar 2)

-- | Typeset a 4-argument judgment.
typeset4 :: forall name modes t1 t2 t3 t4.
            (LogicType t1, LogicType t2, LogicType t3, LogicType t4)
         => (T '[] t1 TypesettingRedex -> T '[] t2 TypesettingRedex -> T '[] t3 TypesettingRedex -> T '[] t4 TypesettingRedex
             -> AppliedM TypesettingRedex name modes '[ '[], '[], '[], '[] ] '[t1, t2, t3, t4])
         -> IO ()
typeset4 j = printRules $ appGoal $ toApplied $ j (modedVar 0) (modedVar 1) (modedVar 2) (modedVar 3)

-- | Typeset a 5-argument judgment.
typeset5 :: forall name modes t1 t2 t3 t4 t5.
            (LogicType t1, LogicType t2, LogicType t3, LogicType t4, LogicType t5)
         => (T '[] t1 TypesettingRedex -> T '[] t2 TypesettingRedex -> T '[] t3 TypesettingRedex -> T '[] t4 TypesettingRedex -> T '[] t5 TypesettingRedex
             -> AppliedM TypesettingRedex name modes '[ '[], '[], '[], '[], '[] ] '[t1, t2, t3, t4, t5])
         -> IO ()
typeset5 j = printRules $ appGoal $ toApplied $ j (modedVar 0) (modedVar 1) (modedVar 2) (modedVar 3) (modedVar 4)

-- | Typeset a 6-argument judgment.
typeset6 :: forall name modes t1 t2 t3 t4 t5 t6.
            (LogicType t1, LogicType t2, LogicType t3, LogicType t4, LogicType t5, LogicType t6)
         => (T '[] t1 TypesettingRedex -> T '[] t2 TypesettingRedex -> T '[] t3 TypesettingRedex -> T '[] t4 TypesettingRedex -> T '[] t5 TypesettingRedex -> T '[] t6 TypesettingRedex
             -> AppliedM TypesettingRedex name modes '[ '[], '[], '[], '[], '[], '[] ] '[t1, t2, t3, t4, t5, t6])
         -> IO ()
typeset6 j = printRules $ appGoal $ toApplied $ j (modedVar 0) (modedVar 1) (modedVar 2) (modedVar 3) (modedVar 4) (modedVar 5)
