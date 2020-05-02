{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE LambdaCase #-}

{-|
 Module : Data.Hashgraph
 Description : Implementation of the Hashgraph ordering algorithm
 License : MIT
 Stability : experimental
 Maintainer : drsk

 This is an implementation of the Hashgraph ordering algorithm as described
 [here](http://www.swirlds.com/downloads/SWIRLDS-TR-2016-01.pdf).

 To order events, you `insert` them into the `Cache`. Once enough events have been inserted, events
 receive a consensus round and time-stamp. Events with received rounds and times are stored in the
 field `cReceivedRoundAndTimes` of the cache.

 The `Cache` needs to be periodically purged to not grow indefinitely.
-}
module Data.Hashgraph
  (
  -- * Hashgraph data structure
  Event(..)

  -- * Cache
  , Cache(..)
  , emptyCache
  , insert
  , purge

  -- * Visualize Hashgraphs with `graphviz`
  , printHG
  ) where

import Control.Monad (void)
import Data.Bits
import Data.Graph.Inductive
import Data.GraphViz
import Data.GraphViz.Attributes.Complete
import qualified Data.IntMap.Strict as IM
import Data.Ix
import Data.List.Extra (find, nubSort, nubSortOn, sort, sortOn)
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import Data.Traversable (for)
import GHC.Generics (Generic)
import Prelude hiding (lookup)
import Safe

----------------------------------------------------------------------------------------------------
-- * Hashgraph data structures

-- | Constraints on event type parameters.
type C a t i s = (C0 a, C0 t, C0 i, C0 s, Bits s, FiniteBits s)
type C0 a = (Eq a, Ord a, Show a)

data Event a t i s = Event
  { payload :: a
  , parents :: Maybe (EventId, EventId)
  , time :: t
  , creator :: i
  , sig :: s
  } deriving (Show, Eq, Generic)
deriving instance C a t i s => Ord (Event a t i s)

----------------------------------------------------------------------------------------------------
-- * Cache

type EventId = T.Text
type Hashgraph a t i s = M.Map EventId (Event a t i s)
type Ancestors = M.Map EventId (S.Set EventId)
type SelfAncestors = M.Map EventId [EventId]
type StronglySees = M.Map EventId (S.Set EventId)
type EventRounds = M.Map EventId Int
type Witnesses = S.Set EventId
type WitnessesByRound = M.Map Int (S.Set EventId)
type Famous = S.Set EventId
type Population = Int

-- | Constants, currently fixed.
d, c :: Int
d = 1
c = 10

-- | The cache contains the hashgraph itself, the received rounds and times as well as additional
-- information that is needed to compute the received rounds and times efficiently. It grows with
-- every insert and needs to be purged periodically.
data Cache a t i s = Cache
  { cHashgraph :: !(Hashgraph a t i s)
    -- the complete hashgraph.
  , cPopulation :: !Int
    -- the number of different identities in the hashgraph.
  , cAncestors :: !Ancestors
    -- all ancestors for a given event.
  , cSelfAncestors :: !SelfAncestors
    -- the self-ancestors for a given event, ordered from newest to oldest.
  , cLatest :: !(M.Map i EventId)
    -- the latest event for a creator
  , cEventsWithChildren :: !(S.Set EventId)
    -- if we try to insert an event that has already been noted here, it's a fork and we need to
    -- remove all of this creators events from the cache.
  , cSees :: !(M.Map EventId (S.Set EventId))
    -- map events to other events it sees.
  , cStronglySees :: !StronglySees
    -- map events to other events it strongly sees.
  , cEventRounds :: !EventRounds
    -- map events to its rounds.
  , cWitnessesByRound :: !WitnessesByRound
    -- map from round to witnesses of that round
  , cWitnesses :: !Witnesses
    -- the set of all witness events
  , cLatestPathCreators :: !(M.Map EventId (M.Map EventId (S.Set i)))
    -- map from head to next witness reachable via a path, counting creators of events in that path.
  , cFamous :: !Famous
    -- the set of all famous events, same as unique famous because we don't allow forks.
  , cFamousByRound :: !(M.Map Int (S.Set EventId))
    -- map from round number to uniquely famous events
  , cMaxRoundDecided :: !Int
    -- the maximal decided round number
  , cNotReceivedRoundYet :: !(S.Set EventId)
    -- events that have not yet received a round and time
  , cReceivedRoundAndTimes :: !(M.Map EventId (Int, t))
    -- the final ordering
  }

-- | The initial empty cache.
emptyCache :: Int -> Cache a t i s
emptyCache n =
  Cache {
    cHashgraph = M.empty
    , cPopulation = n
    , cAncestors = M.empty
    , cSelfAncestors = M.empty
    , cLatest = M.empty
    , cEventsWithChildren = S.empty
    , cSees = M.empty
    , cStronglySees = M.empty
    , cEventRounds = M.empty
    , cWitnessesByRound = M.singleton 0 S.empty
    , cWitnesses = S.empty
    , cLatestPathCreators = M.empty
    , cFamous = S.empty
    , cFamousByRound = M.singleton 0 S.empty
    , cMaxRoundDecided = 0
    , cNotReceivedRoundYet = S.empty
    , cReceivedRoundAndTimes = M.empty
  }

-- | Insert a new event into the cache and update all computed information. Events needs to be
-- inserted in topological order.
insert ::
     C a t i s
  => (Event a t i s -> EventId)
  -> Event a t i s
  -> Cache a t i s
  -> Cache a t i s
insert mkEventId e c0 = c1
  where
    c1 =
      Cache
        { cHashgraph = newHashgraph
        , cAncestors = newAncestors
        , cSelfAncestors = newSelfAncestors
        , cLatest = newLatest
        , cEventsWithChildren = newEventsWithChildren
        , cSees = newAncestors
        , cStronglySees = newStronglySees
        , cEventRounds = newEventRounds
        , cWitnessesByRound = newWitnessesByRound
        , cWitnesses = newWitnesses
        , cLatestPathCreators = newLatestPathCreators
        , cFamous = newFamous
        , cFamousByRound = newFamousByRound
        , cMaxRoundDecided = newMaxRoundDecided
        , cNotReceivedRoundYet = newNotReceivedRoundYet
        , cReceivedRoundAndTimes = newReceivedRoundAndTimes
        , cPopulation = cPopulation c0
        }
    eId = mkEventId e
    eCreator = creator e
    eParents = parents e
    eSelfParentRound = selfParentRound newHashgraph (cEventRounds c0) eId
    eRound
      | doIncrement = eSelfParentRound + 1
      | otherwise = eSelfParentRound
    doIncrement =
      let r = selfParentRound newHashgraph (cEventRounds c0) eId
          s =
            [ y
            | y <- S.toList $ lookup0 "cStronglySees" newStronglySees eId
            , eventRound (cEventRounds c0) y == r
            ]
       in manyCreators newHashgraph (cPopulation c0) s
    isWitness = isNothing eParents || doIncrement
    newHashgraph = M.insert eId e (cHashgraph c0)
    newAncestors =
      M.insert
        eId
        (S.insert eId $
         S.unions
           [ lookup0 "cAncestors" (cAncestors c0) p
           | p <- parentsToList eParents
           ])
        (cAncestors c0)
    newSelfAncestors =
      M.insert
        eId
        ((eId :) $
         maybe [] (lookup0 "cSelfAncestors" (cSelfAncestors c0) . fst) eParents)
        (cSelfAncestors c0)
    newLatest = M.insert (creator e) eId (cLatest c0)
    newEventRounds = M.insert eId eRound (cEventRounds c0)
    newEventsWithChildren
      | eId `S.member` cEventsWithChildren c0 =
        error $ "detected fork for creator: " <> show eCreator
      | otherwise =
        S.fromList [fst ps | Just ps <- [eParents]] `S.union`
        cEventsWithChildren c0
    newWitnesses
      | isWitness = S.insert eId (cWitnesses c0)
      | otherwise = cWitnesses c0
    newWitnessesByRound
      | isWitness =
        M.insertWith S.union eRound (S.singleton eId) (cWitnessesByRound c0)
      | otherwise = cWitnessesByRound c0
    deltaFamous
      | isWitness =
        S.fromList
          [ w
          | w <-
              S.toList $
              S.unions $
              M.elems $
              M.filterWithKey
                (\r _ws -> r > cMaxRoundDecided c0)
                (cWitnessesByRound c0)
          , decide
              newHashgraph
              newAncestors
              newWitnesses
              newWitnessesByRound
              newStronglySees
              newEventRounds
              (cPopulation c0)
              eId
              w &&
              vote
                newHashgraph
                newAncestors
                newWitnesses
                newWitnessesByRound
                newStronglySees
                newEventRounds
                (cPopulation c0)
                eId
                w
          ]
      | otherwise = S.empty
    newFamous
      | isWitness = cFamous c0 `S.union` deltaFamous
      | otherwise = cFamous c0
    newFamousByRound
      | isWitness =
        M.unionWith
          S.union
          (M.fromListWith
             S.union
             [ (eventRound (cEventRounds c0) x, S.singleton x)
             | x <- S.toList deltaFamous
             ])
          (cFamousByRound c0)
      | otherwise = cFamousByRound c0
    newLatestPathCreators
      | isWitness =
        M.insert eId (M.singleton eId (S.singleton eCreator)) $
        cLatestPathCreators c0
      | otherwise = M.insert eId deltaLatestPathCreators $ cLatestPathCreators c0
    deltaLatestPathCreators = -- new entry for eId
      M.unionsWith
        S.union -- if two path go to the same witness event, we union the creators of both path
        ([ M.map (S.insert eCreator) path
         | p <- parentsToList eParents
         , let path = lookup0 "cLatestPaths" (cLatestPathCreators c0) p
         ] ++
         [M.singleton eId (S.singleton eCreator) | isNothing eParents])
    newStronglySees = deltaStronglySees `M.union` cStronglySees c0
    deltaStronglySees =
      M.fromListWith
        S.union
        [ (eId, S.fromList [x | manyCreators0 (cPopulation c0) (S.size cs)])
        | (x, cs) <- M.toList deltaLatestPathCreators
        ]
    newMaxRoundDecided
      | isWitness -- a new maximal decided round can only happen with a new witness
       =
        let wss -- witnesses of rounds greater than the maximal decided round
             =
              [ (n, ws)
              | (n, ws) <- M.toList newWitnessesByRound
              , n > cMaxRoundDecided c0
              ]
         in last $ -- take the maximum round such that all its witnesses have been decided
            cMaxRoundDecided c0 :
            [ n
            | (n, ws) <- sortOn fst wss
            , ws' <- [ws' | (n', ws') <- wss, n' > n + d] -- only later round witnesses can decide
            , and -- all witnessess of round n have been decided by at least one of a later round.
                [ or
                  [ decide
                    newHashgraph
                    newAncestors
                    newWitnesses
                    newWitnessesByRound
                    newStronglySees
                    newEventRounds
                    (cPopulation c0)
                    y
                    x
                  | y <- S.toList ws'
                  ]
                | x <- S.toList ws
                ]
            ]
      | otherwise = cMaxRoundDecided c0
    newWithReceivedRound0 =
      [ lookup0 "newAncestors" newAncestors w
      | w <-
          S.toList $
          lookup0 "newFamousByRound" newFamousByRound newMaxRoundDecided
      ]
    newWithReceivedRound
      | null newWithReceivedRound0 = S.empty
      | otherwise = foldl1 S.intersection newWithReceivedRound0
    newNotReceivedRoundYet =
      S.insert eId $ cNotReceivedRoundYet c0 S.\\ newWithReceivedRound
    newReceivedRoundAndTimes =
      cReceivedRoundAndTimes c0 `M.union`
      M.fromList
         [ (x, (newMaxRoundDecided, computeTime x))
         | x <- S.toList newWithReceivedRound
         ]
    computeTime x =
      median
        [ time $ lookup0 "newHashgraph" newHashgraph y
        | z <-
            S.toList $
            lookup0 "newFamousByRound" newFamousByRound newMaxRoundDecided
        , let ys = lookup0 "newSelfAncestors" newSelfAncestors z
        , let y = last [y | y <- ys, ancestor newAncestors y x]
        ]

-- | Purge all events and information for events that have received a round and time.
purge :: Cache a t i s -> Cache a t i s
purge c =
  c
    { cHashgraph = newHashgraph
    , cAncestors = newAncestors
    , cSelfAncestors = newSelfAncestors
    , cEventsWithChildren = newEventsWithChildren
    , cSees = newAncestors
    , cStronglySees = newStronglySees
    , cEventRounds = newEventRounds
    , cWitnessesByRound = newWitnessesByRound
    , cWitnesses = newWitnesses
    , cFamous = newFamous
    , cFamousByRound = newFamousByRound
    , cReceivedRoundAndTimes = M.empty
    , cPopulation = cPopulation c
    }
  where
    oldEventIds = M.keysSet $ cReceivedRoundAndTimes c
    newHashgraph = M.withoutKeys (cHashgraph c) oldEventIds
    newAncestors = M.withoutKeys (cAncestors c) oldEventIds
    newSelfAncestors = M.withoutKeys (cSelfAncestors c) oldEventIds
    newEventsWithChildren = cEventsWithChildren c S.\\ oldEventIds
    newStronglySees = M.withoutKeys (cStronglySees c) oldEventIds
    newEventRounds = M.withoutKeys (cEventRounds c) oldEventIds
    newWitnessesByRound =
      M.filterWithKey (\k _ -> k >= cMaxRoundDecided c) $ cWitnessesByRound c
    newWitnesses = cWitnesses c S.\\ oldEventIds
    newFamous = cFamous c S.\\ oldEventIds
    newFamousByRound =
      M.filterWithKey (\k _ -> k >= cMaxRoundDecided c) $ cFamousByRound c

----------------------------------------------------------------------------------------------------

supermajority :: Int -> Double
supermajority pop = 2 / 3 * fromIntegral pop

selfParent :: Hashgraph a t i s -> EventId -> Maybe EventId
selfParent hg = fmap fst . parents . lookup0 "cHashgraph" hg

ancestor :: Ancestors -> EventId -> EventId -> Bool
ancestor as x y = y `S.member` lookup0 "cAncestors" as x

selfAncestor :: SelfAncestors -> EventId -> EventId -> Bool
selfAncestor as x y =
  y `S.member` S.fromList (lookup0 "cSelfAncestors" as x)

manyCreators :: C a t i s => Hashgraph a t i s -> Int -> [EventId] -> Bool
manyCreators hg pop s =
  let s' = nubSort $ map (creator . lookup0 "cHashgraph" hg) s
      n = supermajority pop
   in fromIntegral (length s') > n

manyCreators0 :: Int -> Int -> Bool
manyCreators0 pop i = fromIntegral i > supermajority pop

-- we make sure on insertion, that a fork is never inserted in the cache, see cEventsWithChildren.
see :: Ancestors -> EventId -> EventId -> Bool
see = ancestor

stronglySee :: StronglySees -> EventId -> EventId -> Bool
stronglySee ss x y =
  -- see cache x y && -- redundant by construction of cStronglySees
  y `S.member` lookup0 "cStronglySees" ss x

selfParentRound :: Hashgraph a t i s -> EventRounds -> EventId -> Int
selfParentRound hg evrs x =
  maybe 1 (eventRound evrs) (selfParent hg x)

eventRound :: EventRounds -> EventId -> Int
eventRound = lookup0 "cEventRounds"

witness :: Witnesses -> EventId -> Bool
witness ws x = x `S.member` ws

famous :: Famous -> EventId -> Bool
famous fms x = x `S.member` fms

diff :: EventRounds -> EventId -> EventId -> Int
diff evrs x y = eventRound evrs x - eventRound evrs y

fractTrue ::
     C a t i s
  => Hashgraph a t i s
  -> Ancestors
  -> Witnesses
  -> WitnessesByRound
  -> StronglySees
  -> EventRounds
  -> Population
  -> EventId
  -> EventId
  -> Double
fractTrue hg as ws wsByRound ss evrds pop x y =
  fromIntegral (votes hg as ws wsByRound ss evrds pop x y True) /
  max
     1
     (fromIntegral
        (votes hg as ws wsByRound ss evrds pop x y True +
         votes hg as ws wsByRound ss evrds pop x y False))

votes ::
     C a t i s
  => Hashgraph a t i s
  -> Ancestors
  -> Witnesses
  -> WitnessesByRound
  -> StronglySees
  -> EventRounds
  -> Population
  -> EventId
  -> EventId
  -> Bool
  -> Int
votes hg as ws wsByRound ss evrds pop x y v =
  length
    [ z
    | z <- S.toList $ lookup0 "cWitnessesByRound" wsByRound (xRound - 1)
    , stronglySee ss x z
    , vote hg as ws wsByRound ss evrds pop z y == v
    ]
  where
    xRound = lookup0 "cEventRounds" evrds x

decide ::
     C a t i s
  => Hashgraph a t i s
  -> Ancestors
  -> Witnesses
  -> WitnessesByRound
  -> StronglySees
  -> EventRounds
  -> Population
  -> EventId
  -> EventId
  -> Bool
decide hg as ws wsByRound ss evrds pop x y =
  selfParentDecide hg as ws wsByRound ss evrds pop x y ||
  (witness ws x &&
   witness ws y &&
   roundDiff > d &&
   (roundDiff `mod` c) > 0 &&
   (or
      [ fromIntegral (votes hg as ws wsByRound ss evrds pop x y b) >
      supermajority pop
      | b <- [True, False]
      ]))
  where
    roundDiff = diff evrds x y

selfParentDecide ::
     C a t i s
  => Hashgraph a t i s
  -> Ancestors
  -> Witnesses
  -> WitnessesByRound
  -> StronglySees
  -> EventRounds
  -> Population
  -> EventId
  -> EventId
  -> Bool
selfParentDecide hg as ws wsByRound ss evrds pop x y =
  fromMaybe False $ do
    p <- selfParent hg x
    Just $ decide hg as ws wsByRound ss evrds pop p y

vote ::
     C a t i s
  => Hashgraph a t i s
  -> Ancestors
  -> Witnesses
  -> WitnessesByRound
  -> StronglySees
  -> EventRounds
  -> Population
  -> EventId
  -> EventId
  -> Bool
vote hg as ws wsByRound ss evrds pop x y
  | copyVote =
    vote hg as ws wsByRound ss evrds pop (fromJust (selfParent hg x)) y
  | diff evrds x y == d = see as x y
  | diff evrds x y /= d &&
      ((diff evrds x y `mod` c) == 0) &&
      fractTrue hg as ws wsByRound ss evrds pop x y >= 1 / 3 &&
      fractTrue hg as ws wsByRound ss evrds pop x y <= 2 / 3 =
    let s = sig (lookup0 "cHashgraph" hg x)
     in testBit s (finiteBitSize s `div` 2)
  | otherwise = fractTrue hg as ws wsByRound ss evrds pop x y >= 1 / 2
  where
    copyVote =
      not (witness ws x) || selfParentDecide hg as ws wsByRound ss evrds pop x y

----------------------------------------------------------------------------------------------------
-- utilities

lookup0 :: (Show k, Ord k) => String -> M.Map k v -> k -> v
lookup0 mapName m k =
  fromMaybe (error $ "Key " <> show k <> " not known in " <> mapName) $
  M.lookup k m

parentsToList :: Maybe (a, a) -> [a]
parentsToList mbPs = do
  Just (s, p) <- [mbPs]
  [s, p]

median :: Ord a => [a] -> a
median xs = sort xs !! (length xs `div` 2)

----------------------------------------------------------------------------------------------------
-- * Visualization with `graphviz`

newtype VHashgraph a b = VHashgraph
  { unVHashgraph :: IM.IntMap (VNode a b)
  }

data VNode a b = VNode
  { vnLabel :: a
  , vnChildren :: [(b, Int)]
  , vnParent :: [(b, Int)]
  }

instance Graph VHashgraph where
  empty = VHashgraph IM.empty
  isEmpty (VHashgraph m) = IM.size m == 0
  labNodes (VHashgraph m) = [(i, vnLabel n) | (i, n) <- IM.toList m]
  mkGraph lNodes lEdges = insEdges0 lEdges $ insNodes0 lNodes empty
  match n (VHashgraph m) =
    ( do VNode {vnParent, vnLabel, vnChildren} <- IM.lookup n m
         Just (vnParent, n, vnLabel, vnChildren)
    , VHashgraph $ IM.delete n m)

insNodes0 :: [LNode a] -> VHashgraph a b -> VHashgraph a b
insNodes0 ns (VHashgraph m) = VHashgraph $ foldl ins m ns
  where
    ins hg0 (i, a) = IM.insert i (VNode a [] []) hg0

insEdges0 :: [LEdge b] -> VHashgraph a b -> VHashgraph a b
insEdges0 es (VHashgraph m) = VHashgraph $ foldl ins m es
  where
    ins hg0 (n0, n1, b) =
      IM.adjust (\n -> n {vnParent = (b, n0) : vnParent n}) n1 $
      IM.adjust (\n -> n {vnChildren = (b, n1) : vnChildren n}) n0 hg0

cacheToVGraph :: Show i => Cache a t i s -> VHashgraph NodeInfo String
cacheToVGraph Cache {cHashgraph, cWitnesses, cFamous, cEventRounds} =
  mkGraph
    [ ( read $ T.unpack eId
      , NodeInfo
          { niEventId = eId
          , niCreator = show $ creator e
          , niWitness = witness cWitnesses eId
          , niFamous = famous cFamous eId
          , niRound = eventRound cEventRounds eId
          })
    | (eId, e) <- M.toList cHashgraph
    ]
    (concat
       [ [edge1, edge2]
       | (eId, e) <- M.toList cHashgraph
       , Just ps <- [parents e]
       , let edge1 = (fromEventId eId, fromEventId $ fst ps, "s")
       , let edge2 = (fromEventId eId, fromEventId $ snd ps, "p")
       ])

fromEventId :: EventId -> Int
fromEventId = read . T.unpack

data NodeInfo = NodeInfo
  { niEventId :: EventId
  , niCreator :: String
  , niWitness :: Bool
  , niFamous :: Bool
  , niRound :: Int
  }

formatNode :: (Int, NodeInfo) -> Attributes
formatNode (n, NodeInfo {..}) =
  (Label $
   RecordLabel
     [ FieldLabel "\\N"
     , FieldLabel $ TL.pack niCreator
     , FieldLabel $ TL.pack $ show niRound
     ]) :
  [Color [toWColor Green] | niFamous]

formatEdge :: (Int, Int, String) -> Attributes
formatEdge (from, to, l) = [Label $ StrLabel $ TL.pack l]

clustBy :: (Int, NodeInfo) -> NodeCluster (Maybe Int) (Int, NodeInfo)
clustBy n@(i, NodeInfo{..}) = C (if niWitness then Just niRound else Nothing) $ N n

clustId :: Maybe Int -> GraphID
clustId =
  \case
    Nothing -> Str ""
    Just i -> Num $ Int i

-- | Print a Hashgraph with `graphviz`
printHG :: Show i => Maybe FilePath -> Cache a t i s -> IO ()
printHG mbFile c
  | Nothing <- mbFile = runGraphvizCanvas' graph Xlib
  | Just file <- mbFile = void $ runGraphviz graph Png file
  where
    graph =
      graphToDot
        defaultParams
          { fmtNode = formatNode
          , clusterBy = clustBy
          , clusterID = clustId
          , isDotCluster = isJust
          , fmtEdge = formatEdge
          } $
      cacheToVGraph c
