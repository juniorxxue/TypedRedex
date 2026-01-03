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
-- typeset2 polyConfig flipPolar
-- typeset3 polyConfig lookupTmVar
-- typeset5 polyConfig ssub
-- @
module Typeset
  ( TypesetConfig(..)
  , polyConfig
  , typeset2
  , typeset3
  , typeset4
  , typeset5
  , typeset6
  ) where

import Control.Applicative ((<|>))
import TypedRedex.Interp.Typesetting (TypesettingRedex, printRules, modedVar)
import TypedRedex.Interp.Format (TermFormatter(..))
import TypedRedex.Interp.Display (formatWithDisplay)
import TypedRedex.Interp.PrettyPrint (NamingConfig, emptyNaming, namingFor, cycleNames, numberedNames)
import TypedRedex.DSL.Moded (toApplied, T, AppliedM)
import TypedRedex.DSL.Define (Applied(..))
import TypedRedex.Logic (LogicType)
import TypedRedex.Nominal.Prelude (TyNom, Nom)

import Syntax (Ty, Tm, Env, Polar, Context, tyDisplay, polarDisplay, envDisplay, tmDisplay, contextDisplay)

--------------------------------------------------------------------------------
-- TypesetConfig: combines naming + term formatting
--------------------------------------------------------------------------------

-- | Configuration for typesetting: naming scheme + term formatter.
data TypesetConfig = TypesetConfig
  { tsNaming :: NamingConfig
  , tsFormat :: String -> [String] -> Maybe String
  }

-- | Wrapper to use TypesetConfig as TermFormatter
newtype ConfigFormatter = ConfigFormatter (String -> [String] -> Maybe String)

instance TermFormatter ConfigFormatter where
  formatTerm (ConfigFormatter f) name args = f name args

--------------------------------------------------------------------------------
-- Poly configuration
--------------------------------------------------------------------------------

-- | Typesetting configuration for the poly example.
polyConfig :: TypesetConfig
polyConfig = TypesetConfig
  { tsNaming = namingFor @Env    (numberedNames "Γ")
             $ namingFor @Ty     (cycleNames ["A", "B", "C", "D", "E", "F"])
             $ namingFor @Polar  (cycleNames ["p", "q"])
             $ namingFor @TyNom  (cycleNames ["α", "β", "γ", "δ"])
             $ namingFor @Nom    (cycleNames ["x", "y", "z", "w"])
             $ namingFor @Tm     (numberedNames "e")
             $ namingFor @Context (numberedNames "Σ")
             $ emptyNaming
  , tsFormat = \name args ->
      formatWithDisplay tyDisplay name args <|>
      formatWithDisplay polarDisplay name args <|>
      formatWithDisplay envDisplay name args <|>
      formatWithDisplay tmDisplay name args <|>
      formatWithDisplay contextDisplay name args
  }

--------------------------------------------------------------------------------
-- Typeset functions (one per arity)
--------------------------------------------------------------------------------

-- | Typeset a 2-argument judgment.
typeset2 :: forall name modes t1 t2.
            (LogicType t1, LogicType t2)
         => TypesetConfig
         -> (T '[] t1 TypesettingRedex -> T '[] t2 TypesettingRedex
             -> AppliedM TypesettingRedex name modes '[ '[], '[] ] '[t1, t2])
         -> IO ()
typeset2 cfg j = printRules (tsNaming cfg) (ConfigFormatter (tsFormat cfg)) $
  appGoal $ toApplied $ j (modedVar 0) (modedVar 1)

-- | Typeset a 3-argument judgment.
typeset3 :: forall name modes t1 t2 t3.
            (LogicType t1, LogicType t2, LogicType t3)
         => TypesetConfig
         -> (T '[] t1 TypesettingRedex -> T '[] t2 TypesettingRedex -> T '[] t3 TypesettingRedex
             -> AppliedM TypesettingRedex name modes '[ '[], '[], '[] ] '[t1, t2, t3])
         -> IO ()
typeset3 cfg j = printRules (tsNaming cfg) (ConfigFormatter (tsFormat cfg)) $
  appGoal $ toApplied $ j (modedVar 0) (modedVar 1) (modedVar 2)

-- | Typeset a 4-argument judgment.
typeset4 :: forall name modes t1 t2 t3 t4.
            (LogicType t1, LogicType t2, LogicType t3, LogicType t4)
         => TypesetConfig
         -> (T '[] t1 TypesettingRedex -> T '[] t2 TypesettingRedex -> T '[] t3 TypesettingRedex -> T '[] t4 TypesettingRedex
             -> AppliedM TypesettingRedex name modes '[ '[], '[], '[], '[] ] '[t1, t2, t3, t4])
         -> IO ()
typeset4 cfg j = printRules (tsNaming cfg) (ConfigFormatter (tsFormat cfg)) $
  appGoal $ toApplied $ j (modedVar 0) (modedVar 1) (modedVar 2) (modedVar 3)

-- | Typeset a 5-argument judgment.
typeset5 :: forall name modes t1 t2 t3 t4 t5.
            (LogicType t1, LogicType t2, LogicType t3, LogicType t4, LogicType t5)
         => TypesetConfig
         -> (T '[] t1 TypesettingRedex -> T '[] t2 TypesettingRedex -> T '[] t3 TypesettingRedex -> T '[] t4 TypesettingRedex -> T '[] t5 TypesettingRedex
             -> AppliedM TypesettingRedex name modes '[ '[], '[], '[], '[], '[] ] '[t1, t2, t3, t4, t5])
         -> IO ()
typeset5 cfg j = printRules (tsNaming cfg) (ConfigFormatter (tsFormat cfg)) $
  appGoal $ toApplied $ j (modedVar 0) (modedVar 1) (modedVar 2) (modedVar 3) (modedVar 4)

-- | Typeset a 6-argument judgment.
typeset6 :: forall name modes t1 t2 t3 t4 t5 t6.
            (LogicType t1, LogicType t2, LogicType t3, LogicType t4, LogicType t5, LogicType t6)
         => TypesetConfig
         -> (T '[] t1 TypesettingRedex -> T '[] t2 TypesettingRedex -> T '[] t3 TypesettingRedex -> T '[] t4 TypesettingRedex -> T '[] t5 TypesettingRedex -> T '[] t6 TypesettingRedex
             -> AppliedM TypesettingRedex name modes '[ '[], '[], '[], '[], '[], '[] ] '[t1, t2, t3, t4, t5, t6])
         -> IO ()
typeset6 cfg j = printRules (tsNaming cfg) (ConfigFormatter (tsFormat cfg)) $
  appGoal $ toApplied $ j (modedVar 0) (modedVar 1) (modedVar 2) (modedVar 3) (modedVar 4) (modedVar 5)
