
module Data.Array.LM where

import GHC.Types
import GHC.Prim
import GHC.Magic

import Data.Unlifted
import qualified Data.Array.LI as LI
import Data.Array.UndefElem

type role Array representational
data Array a = Array (MutableArray# RealWorld a)

instance Unlifted (Array a) where
  type Rep (Array a) = (MutableArray# RealWorld a)
  to# (Array arr) = arr
  from#           = Array
  {-# inline to# #-}
  {-# inline from# #-}
  defaultElem = empty
  {-# inline defaultElem #-}

new :: forall a.  Int -> a -> IO (Array a)
new (I# i) a = IO (\s -> case newArray# i a s of
    (# s, arr #) -> (# s, Array arr #))

empty :: Array a
empty = Array (runRW# \s -> case newArray# 0# undefElem s of
  (# s, arr #) -> arr)
{-# noinline empty #-}

read :: forall a.  Array a -> Int -> IO a
read (Array arr) (I# i) = IO (readArray# arr i)
{-# inline read #-}

write :: forall a.  Array a -> Int -> a -> IO ()
write (Array arr) (I# i) a = IO \s ->
  case writeArray# arr i a s of
    s -> (# s, () #)
{-# inline write #-}

modify :: forall a.  Array a -> Int -> (a -> a) -> IO ()
modify (Array arr) (I# i) f = IO \s -> case readArray# arr i s of
  (# s, a #) -> case writeArray# arr i (f a) s of
    s -> (# s, () #)
{-# inline modify #-}

modify' :: forall a.  Array a -> Int -> (a -> a) -> IO ()
modify' (Array arr) (I# i) f = IO \s -> case readArray# arr i s of
  (# s, a #) -> let !v = f a in case writeArray# arr i v s of
    s -> (# s, () #)
{-# inline modify' #-}

size :: Array a -> Int
size (Array arr) = I# (sizeofMutableArray# arr)
{-# inline size #-}

thawSlice :: LI.Array a -> Int -> Int -> IO (Array a)
thawSlice (LI.Array arr) (I# start) (I# len) = IO \s ->
  case thawArray# arr start len s of
    (# s, marr #) -> (# s, Array marr #)
{-# inline thawSlice #-}

thaw :: forall a. LI.Array a -> IO (Array a)
thaw arr = thawSlice arr 0 (LI.size arr)
{-# inline thaw #-}

copySlice :: forall a. Array a -> Int -> Array a -> Int -> Int -> IO ()
copySlice (Array src) (I# i) (Array dst) (I# j) (I# len) = IO \s ->
  case copyMutableArray# src i dst j len s of
    s -> (# s, () #)
{-# inline copySlice #-}

sizedThaw :: forall a. Int -> LI.Array a -> IO (Array a)
sizedThaw size arr = thawSlice arr 0 size
{-# inline sizedThaw #-}

unsafeFreeze :: Array a -> IO (LI.Array a)
unsafeFreeze (Array marr) = IO \s -> case unsafeFreezeArray# marr s of
  (# s, arr #) -> (# s, LI.Array arr #)
{-# inline unsafeFreeze #-}

freezeSlice :: Array a -> Int -> Int -> IO (LI.Array a)
freezeSlice (Array marr) (I# start) (I# len) = IO \s ->
  case freezeArray# marr start len s of
    (# s, arr #) -> (# s, (LI.Array arr) #)
{-# inline freezeSlice #-}

freeze :: Array a -> IO (LI.Array a)
freeze arr = freezeSlice arr 0 (size arr)
{-# inline freeze #-}

sizedFreeze :: Int -> Array a -> IO (LI.Array a)
sizedFreeze size arr = freezeSlice arr 0 size
{-# inline sizedFreeze #-}
