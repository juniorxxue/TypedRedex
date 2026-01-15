-- | Mode declarations for judgments.
--
-- Mode checking is performed at runtime by the interpreters.
module TypedRedex.Core.Schedule
  ( Mode(..)
  , ModeList(..)
  , SingModeList(..)
  ) where

-- | Judgment mode: input or output.
data Mode = I | O deriving (Eq, Show)

-- | Term-level list of modes.
data ModeList (ms :: [Mode]) where
  MNil :: ModeList '[]
  (:*) :: Mode -> ModeList ms -> ModeList (m ': ms)
infixr 5 :*

-- | Singleton class: derive term-level ModeList from type-level list.
class SingModeList (ms :: [Mode]) where
  singModeList :: ModeList ms

instance SingModeList '[] where
  singModeList = MNil

instance SingModeList ms => SingModeList ('I ': ms) where
  singModeList = I :* singModeList

instance SingModeList ms => SingModeList ('O ': ms) where
  singModeList = O :* singModeList
