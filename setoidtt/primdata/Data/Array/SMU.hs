
module Data.Array.SMU where

import GHC.Types
import GHC.Prim
import GHC.Magic
import Data.Unlifted

import qualified Data.Array.SIL as SIL
import qualified Data.Array.SIU as SIU
import Data.Array.UndefElem

type role Array representational
data Array a = Array (SmallMutableArray# RealWorld Any)

instance Unlifted (Array a) where
  toUnlifted# (Array arr) = unsafeCoerce# arr
  {-# inline toUnlifted# #-}
  fromUnlifted# arr = Array (unsafeCoerce# arr)
  {-# inline fromUnlifted# #-}
  default# = empty
  {-# inline default# #-}

new :: forall a. Unlifted a => Int -> a -> IO (Array a)
new (I# i) a = case toUnlifted# a of
  a -> IO (\s -> case newSmallArray# i (unsafeCoerce# a) s of
    (# s, arr #) -> (# s, Array arr #))

empty :: Array a
empty = Array (runRW# $ \s -> case newSmallArray# 0# undefElem s of
  (# s, arr #) -> arr)
{-# noinline empty #-}

read :: forall a. Unlifted a => Array a -> Int -> IO a
read (Array arr) (I# i) = IO $ \s -> case readSmallArray# arr i s of
  (# s, a #) -> case fromUnlifted# (unsafeCoerce# a) of
    !a -> (# s, a #)
{-# inline read #-}

write :: forall a. Unlifted a => Array a -> Int -> a -> IO ()
write (Array arr) (I# i) a = case toUnlifted# a of
  a -> IO $ \s -> case writeSmallArray# arr i (unsafeCoerce# a) s of
    s -> (# s, () #)
{-# inline write #-}

modify :: forall a. Unlifted a => Array a -> Int -> (a -> a) -> IO ()
modify (Array arr) (I# i) f = IO $ \s -> case readSmallArray# arr i s of
  (# s, a #) -> case fromUnlifted# (unsafeCoerce# a) of
    !a -> case toUnlifted# $! (f a) of
      a -> case writeSmallArray# arr i (unsafeCoerce# a) s of
        a -> (# s, () #)
{-# inline modify #-}

size :: Array a -> Int
size (Array arr) = I# (sizeofSmallMutableArray# arr)
{-# inline size #-}

thawSlice :: SIU.Array a -> Int -> Int -> IO (Array a)
thawSlice (SIU.Array (SIL.Array arr)) (I# start) (I# len) = IO $ \s ->
  case thawSmallArray# arr start len s of
    (# s, marr #) -> (# s, Array marr #)
{-# inline thawSlice #-}

thaw :: forall a. SIU.Array a -> IO (Array a)
thaw arr = thawSlice arr 0 (SIU.size arr)
{-# inline thaw #-}

copySlice :: forall a. Array a -> Int -> Array a -> Int -> Int -> IO ()
copySlice (Array src) (I# i) (Array dst) (I# j) (I# len) = IO $ \s ->
  case copySmallMutableArray# src i dst j len s of
    s -> (# s, () #)
{-# inline copySlice #-}

sizedThaw :: forall a. Int -> SIU.Array a -> IO (Array a)
sizedThaw size arr = thawSlice arr 0 size
{-# inline sizedThaw #-}

unsafeFreeze :: Array a -> IO (SIU.Array a)
unsafeFreeze (Array marr) = IO $ \s -> case unsafeFreezeSmallArray# marr s of
  (# s, arr #) -> (# s, SIU.Array (SIL.Array arr) #)
{-# inline unsafeFreeze #-}

freezeSlice :: Array a -> Int -> Int -> IO (SIU.Array a)
freezeSlice (Array marr) (I# start) (I# len) = IO $ \s ->
  case freezeSmallArray# marr start len s of
    (# s, arr #) -> (# s, SIU.Array (SIL.Array arr) #)
{-# inline freezeSlice #-}

freeze :: Array a -> IO (SIU.Array a)
freeze arr = freezeSlice arr 0 (size arr)
{-# inline freeze #-}

sizedFreeze :: Int -> Array a -> IO (SIU.Array a)
sizedFreeze size arr = freezeSlice arr 0 size
{-# inline sizedFreeze #-}
