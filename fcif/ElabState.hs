
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

newMeta :: VTy -> U -> IO MId
newMeta a au = do
  m <- readIORef nextMId
  writeIORef nextMId $! (m + 1)
  alterMeta m (maybe (Just (Unsolved a au)) (\_ -> error "impossible"))
  pure m

------------------------------------------------------------

ucxt :: IORef UCxt
ucxt = runIO (newIORef mempty)
{-# noinline ucxt #-}

nextUId :: IORef Int
nextUId = runIO (newIORef 0)
{-# noinline nextUId #-}

lookupU:: UId -> IO (Maybe U)
lookupU m = do
  ms <- readIORef ucxt
  case IM.lookup m ms of
    Just e -> pure e
    _      -> error "impossible"

runLookupU :: UId -> Maybe U
runLookupU m = runIO (lookupU m)

alterU :: UId -> (Maybe (Maybe U) -> Maybe (Maybe U)) -> IO ()
alterU m f = modifyIORef' ucxt (IM.alter f m)

modifyU :: UId -> (Maybe U -> Maybe U) -> IO ()
modifyU m f = alterU m (maybe (error "impossible") (Just . f))

writeU :: UId -> Maybe U -> IO ()
writeU m e = modifyU m (const e)

newU :: IO UId
newU = do
  m <- readIORef nextUId
  writeIORef nextUId $! (m + 1)
  alterU m (maybe (Just Nothing) (\_ -> error "impossible"))
  pure m

------------------------------------------------------------

reset :: IO ()
reset = do
  writeIORef mcxt mempty
  writeIORef nextMId 0
  writeIORef ucxt mempty
  writeIORef nextUId 0
