
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

writeMeta :: MId -> MetaEntry -> IO ()
writeMeta m e = modifyIORef' mcxt (IM.alter go m) where
  go Just{} = Just e
  go _      = error "impossible"

newMetaEntry :: MetaEntry -> IO MId
newMetaEntry e = do
  m <- readIORef nextMId
  writeIORef nextMId $! (m + 1)
  let f = maybe (Just e) (\_ -> error "impossible")
  modifyIORef' mcxt (IM.alter f m)
  pure m

modifyMeta :: MId -> (MetaEntry -> MetaEntry) -> IO ()
modifyMeta m f = modifyIORef' mcxt (IM.alter go m) where
  go Nothing  = error "impossible"
  go (Just e) = Just (f e)

reset :: IO ()
reset = do
  writeIORef mcxt mempty
  writeIORef nextMId 0
