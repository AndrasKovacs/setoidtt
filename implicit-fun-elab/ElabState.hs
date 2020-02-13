
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

lookupMetaIO :: MId -> IO MetaEntry
lookupMetaIO m = do
  ms <- readIORef mcxt
  case IM.lookup m ms of
    Just e -> pure e
    _      -> error "impossible"

lookupMeta :: MId -> MetaEntry
lookupMeta m = runIO (lookupMetaIO m)

writeMetaIO :: MId -> MetaEntry -> IO ()
writeMetaIO m e = modifyIORef' mcxt (IM.insert m e)

reset :: IO ()
reset = do
  writeIORef mcxt mempty
  writeIORef nextMId 0
