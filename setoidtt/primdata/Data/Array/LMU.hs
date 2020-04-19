
module Data.Array.LMU where

import GHC.Types
import GHC.Prim
import GHC.Magic
import Data.Unlifted

import qualified Data.Array.LIL as LIL
import qualified Data.Array.LIU as LIU
import Data.Array.UndefElem

type role Array representational
data Array a = Array (MutableArray# RealWorld Any)

instance Unlifted (Array a) where
  toUnlifted# (Array arr) = unsafeCoerce# arr
  {-# inline toUnlifted# #-}
  fromUnlifted# arr = Array (unsafeCoerce# arr)
  {-# inline fromUnlifted# #-}
  default# = empty
  {-# inline default# #-}

new :: forall a. Unlifted a => Int -> a -> IO (Array a)
new (I# i) a = case toUnlifted# a of
  a -> IO (\s -> case newArray# i (unsafeCoerce# a) s of
    (# s, arr #) -> (# s, Array arr #))

empty :: Array a
empty = runRW# $ \s -> case newArray# 0# undefElem s of
  (# s, arr #) -> Array arr
{-# noinline empty #-}

read :: forall a. Unlifted a => Array a -> Int -> IO a
read (Array arr) (I# i) = IO $ \s -> case readArray# arr i s of
  (# s, a #) -> case fromUnlifted# (unsafeCoerce# a) of
    !a -> (# s, a #)
{-# inline read #-}

write :: forall a. Unlifted a => Array a -> Int -> a -> IO ()
write (Array arr) (I# i) a = case toUnlifted# a of
  a -> IO $ \s -> case writeArray# arr i (unsafeCoerce# a) s of
    s -> (# s, () #)
{-# inline write #-}

modify :: forall a. Unlifted a => Array a -> Int -> (a -> a) -> IO ()
modify (Array arr) (I# i) f = IO $ \s -> case readArray# arr i s of
  (# s, a #) -> case fromUnlifted# (unsafeCoerce# a) of
    !a -> case toUnlifted# $! (f a) of
      a -> case writeArray# arr i (unsafeCoerce# a) s of
        a -> (# s, () #)
{-# inline modify #-}

size :: Array a -> Int
size (Array arr) = I# (sizeofMutableArray# arr)
{-# inline size #-}

thawSlice :: LIU.Array a -> Int -> Int -> IO (Array a)
thawSlice (LIU.Array (LIL.Array arr)) (I# start) (I# len) = IO $ \s ->
  case thawArray# arr start len s of
    (# s, marr #) -> (# s, Array marr #)
{-# inline thawSlice #-}

thaw :: forall a. LIU.Array a -> IO (Array a)
thaw arr = thawSlice arr 0 (LIU.size arr)
{-# inline thaw #-}

copySlice :: forall a. Array a -> Int -> Array a -> Int -> Int -> IO ()
copySlice (Array src) (I# i) (Array dst) (I# j) (I# len) = IO $ \s ->
  case copyMutableArray# src i dst j len s of
    s -> (# s, () #)
{-# inline copySlice #-}

sizedThaw :: forall a. Int -> LIU.Array a -> IO (Array a)
sizedThaw size arr = thawSlice arr 0 size
{-# inline sizedThaw #-}

unsafeFreeze :: Array a -> IO (LIU.Array a)
unsafeFreeze (Array marr) = IO $ \s -> case unsafeFreezeArray# marr s of
  (# s, arr #) -> (# s, LIU.Array (LIL.Array arr) #)
{-# inline unsafeFreeze #-}

freezeSlice :: Array a -> Int -> Int -> IO (LIU.Array a)
freezeSlice (Array marr) (I# start) (I# len) = IO $ \s ->
  case freezeArray# marr start len s of
    (# s, arr #) -> (# s, LIU.Array (LIL.Array arr) #)
{-# inline freezeSlice #-}

freeze :: Array a -> IO (LIU.Array a)
freeze arr = freezeSlice arr 0 (size arr)
{-# inline freeze #-}

sizedFreeze :: Int -> Array a -> IO (LIU.Array a)
sizedFreeze size arr = freezeSlice arr 0 size
{-# inline sizedFreeze #-}
