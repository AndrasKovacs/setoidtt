
module ElabState where

import Data.IORef
import System.IO.Unsafe
import qualified Data.IntMap.Strict as IM

import Types

mcxt :: IORef MCxt
mcxt = unsafeDupablePerformIO (newIORef mempty)
{-# noinline mcxt #-}

nextMId :: IORef Int
nextMId = unsafeDupablePerformIO (newIORef 0)
{-# noinline nextMId #-}

lookupMetaIO :: MId -> IO MetaEntry
lookupMetaIO m = do
  ms <- readIORef mcxt
  case IM.lookup m ms of
    Just e -> pure e
    _      -> error "impossible"

lookupMeta :: MId -> MetaEntry
lookupMeta m = unsafeDupablePerformIO (lookupMetaIO m)

writeMetaIO :: MId -> MetaEntry -> IO ()
writeMetaIO m e = modifyIORef' mcxt (IM.insert m e)

reset :: IO ()
reset = do
  writeIORef mcxt mempty
  writeIORef nextMId 0
