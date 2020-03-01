
-- | Top-level mutable state involved in elaboration. We use actual mutable
--   top-level references simply because it's convenient and our simple
--   program does not call for anything more sophisticated.

module ElabState where

import Data.IORef
import System.IO.Unsafe
import qualified Data.IntMap.Strict as IM

import Types

runIO :: IO a -> a
runIO = unsafeDupablePerformIO

mcxt :: IORef MCxt
mcxt = runIO (newIORef mempty)
{-# noinline mcxt #-}

nextMId :: IORef Int
nextMId = runIO (newIORef 0)
{-# noinline nextMId #-}

lookupMeta :: MId -> IO MetaEntry
lookupMeta m = do
  ms <- readIORef mcxt
  case IM.lookup m ms of
    Just e -> pure e
    _      -> error "impossible"

runLookupMeta :: MId -> MetaEntry
runLookupMeta m = runIO (lookupMeta m)

alterMeta :: MId -> (Maybe MetaEntry -> Maybe MetaEntry) -> IO ()
alterMeta m f = modifyIORef' mcxt (IM.alter f m)

modifyMeta :: MId -> (MetaEntry -> MetaEntry) -> IO ()
modifyMeta m f = alterMeta m (maybe (error "impossible") (Just . f))

writeMeta :: MId -> MetaEntry -> IO ()
writeMeta m e = modifyMeta m (const e)

newMeta :: MetaEntry -> IO MId
newMeta e = do
  m <- readIORef nextMId
  writeIORef nextMId $! (m + 1)
  alterMeta m (maybe (Just e) (\_ -> error "impossible"))
  pure m

reset :: IO ()
reset = do
  writeIORef mcxt mempty
  writeIORef nextMId 0
