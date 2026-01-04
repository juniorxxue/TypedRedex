{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Pretty-printing utilities for variable naming.
--
-- Provides infinite name sequences for typesetting logic variables.
-- Users can customize naming per-type using 'NamingConfig'.
module TypedRedex.Interp.PrettyPrint
  ( -- * Subscript conversion
    subscriptNum
  , subscriptStr
    -- * Variable naming (infinite lists)
  , VarNames
  , cycleNames
  , numberedNames
  , numberedNames'
    -- * Naming configuration
  , NamingConfig
  , emptyNaming
  , namingFor
  , lookupNaming
  ) where

import Data.Typeable (Typeable, TypeRep, typeRep)
import Data.Proxy (Proxy(..))
import qualified Data.Map.Strict as M

-- | Convert an Int to subscript digits.
-- @subscriptNum 42 = "₄₂"@
subscriptNum :: Int -> String
subscriptNum = subscriptStr . show

-- | Convert a String of digits to subscript.
-- @subscriptStr "123" = "₁₂₃"@
subscriptStr :: String -> String
subscriptStr = concatMap toSub
  where
    toSub '0' = "₀"; toSub '1' = "₁"; toSub '2' = "₂"; toSub '3' = "₃"
    toSub '4' = "₄"; toSub '5' = "₅"; toSub '6' = "₆"; toSub '7' = "₇"
    toSub '8' = "₈"; toSub '9' = "₉"; toSub c = [c]

--------------------------------------------------------------------------------
-- Variable naming (infinite lists)
--------------------------------------------------------------------------------

-- | Infinite list of variable names.
--
-- All naming schemes produce infinite lists, so indexing is always safe.
type VarNames = [String]

-- | Create names that cycle through a list, adding subscripts on overflow.
--
-- @
-- cycleNames ["A", "B", "C"]
--   = ["A", "B", "C", "A₁", "B₁", "C₁", "A₂", "B₂", "C₂", ...]
-- @
cycleNames :: [String] -> VarNames
cycleNames [] = numberedNames "?"  -- Fallback for empty list
cycleNames bases =
  [ base ++ suffix i
  | i <- [0..]
  , base <- bases
  ]
  where
    suffix 0 = ""
    suffix n = subscriptNum n

-- | Create numbered names, with the first one unsubscripted.
--
-- @
-- numberedNames "τ" = ["τ", "τ₁", "τ₂", "τ₃", ...]
-- @
numberedNames :: String -> VarNames
numberedNames sym = sym : [sym ++ subscriptNum i | i <- [1..]]

-- | Backwards-compatible alias for 'numberedNames'.
--
-- @
-- numberedNames' "τ" = ["τ", "τ₁", "τ₂", "τ₃", ...]
-- @
numberedNames' :: String -> VarNames
numberedNames' = numberedNames

--------------------------------------------------------------------------------
-- Naming configuration
--------------------------------------------------------------------------------

-- | Configuration mapping types to their naming schemes.
--
-- Build using 'emptyNaming' and 'namingFor':
--
-- @
-- myNaming :: NamingConfig
-- myNaming = namingFor \@Ty  (cycleNames ["A", "B", "C"])
--          $ namingFor \@Env (cycleNames ["Γ", "Δ", "Θ"])
--          $ emptyNaming
-- @
newtype NamingConfig = NamingConfig (M.Map TypeRep VarNames)

-- | Empty naming configuration. Uses "?₀", "?₁", ... for all types.
emptyNaming :: NamingConfig
emptyNaming = NamingConfig M.empty

-- | Add naming for a specific type.
--
-- @
-- namingFor \@Ty (cycleNames ["A", "B", "C"]) config
-- @
namingFor :: forall a. Typeable a => VarNames -> NamingConfig -> NamingConfig
namingFor names (NamingConfig m) =
  NamingConfig (M.insert (typeRep (Proxy @a)) names m)

-- | Look up naming for a type. Returns default "?₀", "?₁", ... if not found.
lookupNaming :: TypeRep -> NamingConfig -> VarNames
lookupNaming tyRep (NamingConfig m) =
  M.findWithDefault (numberedNames "?") tyRep m
