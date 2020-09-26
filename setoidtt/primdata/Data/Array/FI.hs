
module Data.Array.FI where

import GHC.Types
import GHC.Magic
import GHC.Prim

import Data.Flat
import Data.Unlifted

type role Array representational
data Array a = Array ByteArray#

instance Unlifted (Array a) where
  type Rep (Array a) = ByteArray#
  to# (Array arr) = arr
  from#           = Array
  {-# inline to# #-}
  {-# inline from# #-}
  defaultElem = empty
  {-# inline defaultElem #-}

instance (Flat a, Show a) => Show (Array a) where
  show = show . Data.Array.FI.foldr (:) []
  {-# inline show #-}

new# :: forall a. Flat a => Int# -> ByteArray#
new# n = runRW# \s -> case newByteArray# (n *# Data.Flat.size# @a proxy#) s of
    (# s, marr #) -> case unsafeFreezeByteArray# marr s of
      (# _, arr #) -> arr
{-# inline new# #-}

new :: forall a. Flat a => Int -> Array a
new (I# n) = Array (new# @a n)
{-# inline new #-}

empty :: Array a
empty = Array (runRW# \s -> case newByteArray# 0# s of
    (# s, marr #) -> case unsafeFreezeByteArray# marr s of
      (# _, arr #) -> arr)
{-# noinline empty #-}

infixl 7 !#
(!#) :: forall a. Flat a => ByteArray# -> Int# -> a
(!#) arr i = indexByteArray# @a arr i
{-# inline (!#) #-}

infixl 7 !
(!) :: forall a. Flat a => Array a -> Int -> a
(!) (Array arr) (I# i) = indexByteArray# @a arr i
{-# inline (!) #-}

size# :: forall a. Flat a => ByteArray# -> Int#
size# arr = quotInt# (sizeofByteArray# arr) (Data.Flat.size# @a proxy#)
{-# inline size# #-}

size :: forall a. Flat a => Array a -> Int
size (Array arr) = I# (Data.Array.FI.size# @a arr)
{-# inline size #-}

sizedMap# :: forall a b. (Flat a, Flat b) => Int# -> (a -> b) -> ByteArray# -> ByteArray#
sizedMap# size f = \arr ->
    let go :: Int# -> MutableByteArray# s -> Int# -> State# s -> State# s
        go i marr size s = case i <# size of
            1# -> case writeByteArray# marr i (f ((!#) @a arr i)) s of
                s -> go (i +# 1#) marr size s
            _  -> s
    in runRW# \s ->
        case newByteArray# (size *# (Data.Flat.size# @a proxy#)) s of
            (# s, marr #) -> case go 0# marr size s of
                s -> case unsafeFreezeByteArray# marr s of
                  (# _, arr #) -> arr
{-# inline sizedMap# #-}

sizedMap :: forall a b. (Flat a, Flat b) => Int -> (a -> b) -> Array a -> Array b
sizedMap (I# s) f = \(Array arr) -> Array (sizedMap# s f arr)
{-# inline sizedMap #-}

map :: forall a b. (Flat a, Flat b) => (a -> b) -> Array a -> Array b
map f = \arr -> sizedMap @a @b (Data.Array.FI.size arr) f arr
{-# inline map #-}

foldr :: forall a b. Flat a => (a -> b -> b) -> b -> Array a -> b
foldr f = \z (Array arr) -> go 0# (Data.Array.FI.size# @a arr) z arr where
    go i s z arr = case i <# s of
        1# -> f (arr !# i :: a) (go (i +# 1#) s z arr)
        _  -> z
{-# inline foldr #-}

rfoldr :: forall a b. Flat a => (a -> b -> b) -> b -> Array a -> b
rfoldr f = \z (Array arr) -> go (Data.Array.FI.size# @a arr -# 1#) z arr where
    go i z arr = case i >=# 0# of
        1# -> f (arr !# i :: a) (go (i -# 1#) z arr)
        _  -> z
{-# inline rfoldr #-}

foldl' :: forall a b. Flat a => (b -> a -> b) -> b -> Array a -> b
foldl' f = \z (Array arr) -> go 0# (Data.Array.FI.size# @a arr) z arr  where
    go i s !z arr = case i <# s of
        1# -> go (i +# 1#) s (f z (arr !# i :: a)) arr
        _  -> z
{-# inline foldl' #-}

rfoldl' :: forall a b. Flat a => (b -> a -> b) -> b -> Array a -> b
rfoldl' f = \z (Array arr) -> go (Data.Array.FI.size# @a arr -# 1#) z arr where
    go i !z arr = case i >=# 0# of
        1# -> go (i -# 1#) (f z (arr !# i :: a)) arr
        _  -> z
{-# inline rfoldl' #-}

fromList :: forall a. Flat a => [a] -> Array a
fromList xs = case length xs of
  I# len -> Array (runRW# \s ->
    case newByteArray# (Data.Flat.size# @a proxy# *# len) s of
      (# s, marr #) -> go xs 0# s where
        go (x:xs) i s = case Data.Flat.writeByteArray# marr i x s of
                          s -> go xs (i +# 1#) s
        go _      _ s = case unsafeFreezeByteArray# marr s of (# _, arr #) -> arr)
{-# inline fromList #-}
