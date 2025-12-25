{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

-- | Hash (freshness) constraints for nominal logic.
--
-- This module re-exports 'Hash' from the logic layer.
module TypedRedex.Nominal.Hash
  ( Hash(..)
  ) where

import TypedRedex.Logic.Nominal (Hash(..))
