-- | Mode declarations and premise scheduling utilities.
module TypedRedex.Core.Schedule
  ( Mode(..)
  , ModeList(..)
  , SingModeList(..)
  , Schedulable(..)
  , ScheduleAmbiguity(..)
  , ScheduleBlocked(..)
  , ScheduleReport(..)
  , schedulePremises
  , schedulePremisesReport
  ) where

import Data.Set (Set)
import qualified Data.Set as S

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

--------------------------------------------------------------------------------
-- Scheduling utilities (mode-based)
--------------------------------------------------------------------------------

class Schedulable a where
  schedReqVars :: a -> Set Int
  schedProdVars :: a -> Set Int
  schedDesc :: a -> String

data ScheduleAmbiguity = ScheduleAmbiguity
  { saChoices :: [String]
  }

data ScheduleBlocked = ScheduleBlocked
  { sbBlockedVars :: Set Int
  , sbGhostInputs :: Set Int
  , sbBlockedPremises :: [String]
  }

data ScheduleReport a = ScheduleReport
  { srOrdered :: [a]
  , srAmbiguities :: [ScheduleAmbiguity]
  , srBlocked :: Maybe ScheduleBlocked
  }

schedulePremises :: Schedulable a => Set Int -> [a] -> [a]
schedulePremises avail prems =
  srOrdered (schedulePremisesReport avail prems)

schedulePremisesReport :: Schedulable a => Set Int -> [a] -> ScheduleReport a
schedulePremisesReport avail prems =
  go avail prems [] []
  where
    go _ [] ordered ambigs =
      ScheduleReport (reverse ordered) (reverse ambigs) Nothing
    go avail' ps ordered ambigs =
      case selectReadyWithChoices avail' ps of
        Nothing ->
          let blocked = computeBlocked avail' ps
              ordered' = reverse ordered ++ ps
          in ScheduleReport ordered' (reverse ambigs) (Just blocked)
        Just (ready, rest, choices) ->
          let ambigs' =
                if length choices > 1
                  then ScheduleAmbiguity (map schedDesc choices) : ambigs
                  else ambigs
              avail'' = S.union avail' (schedProdVars ready)
          in go avail'' rest (ready : ordered) ambigs'

    selectReadyWithChoices :: Schedulable a => Set Int -> [a] -> Maybe (a, [a], [a])
    selectReadyWithChoices avail' ps =
      case selectReady avail' ps of
        Nothing -> Nothing
        Just (ready, rest) ->
          let choices = filter (isReady avail') ps
          in Just (ready, rest, choices)

    selectReady :: Schedulable a => Set Int -> [a] -> Maybe (a, [a])
    selectReady _ [] = Nothing
    selectReady avail' (p:ps)
      | isReady avail' p = Just (p, ps)
      | otherwise = case selectReady avail' ps of
          Nothing -> Nothing
          Just (ready, rest) -> Just (ready, p : rest)

    isReady :: Schedulable a => Set Int -> a -> Bool
    isReady avail' p = schedReqVars p `S.isSubsetOf` avail'

    computeBlocked :: Schedulable a => Set Int -> [a] -> ScheduleBlocked
    computeBlocked avail' ps =
      let blockedPrems = filter (\p -> not (isReady avail' p)) ps
          reqs = S.unions (map schedReqVars blockedPrems)
          blockedVars = S.difference reqs avail'
          prod = S.unions (map schedProdVars ps)
          ghostInputs = S.difference blockedVars prod
      in ScheduleBlocked
           { sbBlockedVars = blockedVars
           , sbGhostInputs = ghostInputs
           , sbBlockedPremises = map schedDesc blockedPrems
           }
