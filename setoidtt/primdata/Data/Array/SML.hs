
module Data.Array.SML where

import GHC.Types
import GHC.Prim
import GHC.Magic

import Data.Unlifted
import qualified Data.Array.SIL as SIL

type role Array representational
data Array a = Array (SmallMutableArray# RealWorld a)

instance Unlifted (Array a) where
  toUnlifted# (Array arr) = unsafeCoerce# arr
  {-# inline toUnlifted# #-}
  fromUnlifted# arr = Array (unsafeCoerce# arr)
  {-# inline fromUnlifted# #-}

new :: forall a.  Int -> a -> IO (Array a)
new (I# i) a = IO (\s -> case newSmallArray# i a s of
    (# s, arr #) -> (# s, Array arr #))

empty :: Array a
empty = runRW# $ \s -> case newSmallArray# 0# SIL.undefElem s of
  (# s, arr #) -> Array arr
{-# noinline empty #-}

read :: forall a.  Array a -> Int -> IO a
read (Array arr) (I# i) = IO (readSmallArray# arr i)
{-# inline read #-}

write :: forall a.  Array a -> Int -> a -> IO ()
write (Array arr) (I# i) a = IO $ \s ->
  case writeSmallArray# arr i a s of
    s -> (# s, () #)
{-# inline write #-}

modify :: forall a.  Array a -> Int -> (a -> a) -> IO ()
modify (Array arr) (I# i) f = IO $ \s -> case readSmallArray# arr i s of
  (# s, a #) -> case writeSmallArray# arr i (f a) s of
    s -> (# s, () #)
{-# inline modify #-}

modify' :: forall a.  Array a -> Int -> (a -> a) -> IO ()
modify' (Array arr) (I# i) f = IO $ \s -> case readSmallArray# arr i s of
  (# s, a #) -> let !v = f a in case writeSmallArray# arr i v s of
    s -> (# s, () #)
{-# inline modify' #-}

size :: Array a -> Int
size (Array arr) = I# (sizeofSmallMutableArray# arr)
{-# inline size #-}

thawSlice :: SIL.Array a -> Int -> Int -> IO (Array a)
thawSlice (SIL.Array arr) (I# start) (I# len) = IO $ \s ->
  case thawSmallArray# arr start len s of
    (# s, marr #) -> (# s, Array marr #)
{-# inline thawSlice #-}

thaw :: forall a. SIL.Array a -> IO (Array a)
thaw arr = thawSlice arr 0 (SIL.size arr)
{-# inline thaw #-}

sizedThaw :: forall a. Int -> SIL.Array a -> IO (Array a)
sizedThaw size arr = thawSlice arr 0 size
{-# inline sizedThaw #-}

unsafeFreeze :: Array a -> IO (SIL.Array a)
unsafeFreeze (Array marr) = IO $ \s -> case unsafeFreezeSmallArray# marr s of
  (# s, arr #) -> (# s, SIL.Array arr #)
{-# inline unsafeFreeze #-}

freezeSlice :: Array a -> Int -> Int -> IO (SIL.Array a)
freezeSlice (Array marr) (I# start) (I# len) = IO $ \s ->
  case freezeSmallArray# marr start len s of
    (# s, arr #) -> (# s, (SIL.Array arr) #)
{-# inline freezeSlice #-}

freeze :: Array a -> IO (SIL.Array a)
freeze arr = freezeSlice arr 0 (size arr)
{-# inline freeze #-}

sizedFreeze :: Int -> Array a -> IO (SIL.Array a)
sizedFreeze size arr = freezeSlice arr 0 size
{-# inline sizedFreeze #-}
