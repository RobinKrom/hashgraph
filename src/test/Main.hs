{-# LANGUAGE NamedFieldPuns #-}
module Main where

import Control.Concurrent (threadDelay)
import Control.Monad
import Data.GraphViz
import Data.Hashgraph
import Data.IORef
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import Data.Time.Clock.POSIX (getCurrentTime)
import System.Random

parties :: [String]
parties = ["alice", "bob", "charlie", "doris", "eve"]

randomParty :: [String] -> IO String
randomParty ps = do
  i <- randomRIO (0, length ps - 1)
  pure $ ps !! i

main :: IO ()
main = do
  cacheRef <- newIORef $ emptyCache $ length parties
  forM_ [0 :: Int .. 100] $ \i -> do
    t <- getCurrentTime
    cache0@Cache {cLatest} <- readIORef cacheRef
    p <- randomParty parties
    parentP <- randomParty $ filter (/= p) parties
    let mbSelfParent = M.lookup p cLatest
    let mbParent = M.lookup parentP cLatest
    let mbE
          | Nothing <- mbSelfParent =
            Just $
            Event
              { payload = i
              , time = t
              , creator = p
              , sig = i
              , parents = Nothing
              }
          | Just selfParent <- mbSelfParent = do
            parent <- mbParent
            Just $
              Event
                { payload = i
                , time = t
                , creator = p
                , sig = i
                , parents = Just (selfParent, parent)
                }
    let mkEventId = const $ T.pack $ show i
    let newCache = maybe cache0 (\e -> insert mkEventId e cache0) mbE
    atomicWriteIORef cacheRef newCache
    print $ M.toList $ cReceivedRoundAndTimes newCache
  finalCache <- readIORef cacheRef
  printHG Nothing finalCache
