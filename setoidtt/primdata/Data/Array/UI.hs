
module Data.Array.UI where

import GHC.Types
import GHC.Magic
import GHC.Prim
import Data.Unlifted

type role Array representational
data Array a = Array ArrayArray#

instance Unlifted (Array a) where
  type Rep (Array a) = ArrayArray#
  to# (Array arr) = arr
  from# arr       = Array arr
  {-# inline to# #-}
  {-# inline from# #-}
  defaultElem = empty
  {-# inline defaultElem #-}

instance (Unlifted a, Show a) => Show (Array a) where
  show = show . Data.Array.UI.foldr (:) []
  {-# inline show #-}

new :: forall a. Unlifted a => Int -> a -> Array a
new (I# i) a = case to# a of
  a -> Array (runRW# \s -> case newUnlifted# i a s of
         (# s, marr #) -> case unsafeFreezeArrayArray# marr s of
           (# s, arr #) -> arr)
{-# inline new #-}

empty :: Array a
empty = Array (runRW# \s -> case newArrayArray# 0# s of
         (# s, marr #) -> case unsafeFreezeArrayArray# marr s of
           (# s, arr #) -> arr)
{-# noinline empty #-}

infixl 7 !
(!) :: Unlifted a => Array a -> Int -> a
(!) (Array arr) (I# i) = from# (indexUnlifted# arr i)
{-# inline (!) #-}

size :: Array a -> Int
size (Array arr) = I# (sizeofArrayArray# arr)
{-# inline size #-}

-- | Create a new array from a slice of the input array.
--   `Int` arguments are: offset, slice length.
clone :: Unlifted a => Array a -> Int -> Int -> Array a
clone (Array arr) (I# i) (I# l) =
  Array (runRW# \s -> case newArrayArray# l s of
     (# s, marr #) -> case copyArrayArray# arr i marr 0# l s of
       s -> case unsafeFreezeArrayArray# marr s of
         (# s, arr #) -> arr)
{-# inline clone #-}


foldr :: forall a b. Unlifted a => (a -> b -> b) -> b -> Array a -> b
foldr f z = \(Array arr) -> go 0# (sizeofArrayArray# arr) z arr where
    go :: Int# -> Int# -> b -> ArrayArray# -> b
    go i s z arr = case i <# s of
        1# -> case indexUnlifted# arr i of
                a -> case from# a of
                  !a -> f a (go (i +# 1#) s z arr)
        _  -> z
{-# inline foldr #-}

foldl' :: forall a b. Unlifted a => (b -> a -> b) -> b -> Array a -> b
foldl' f z = \(Array arr) -> go 0# (sizeofArrayArray# arr) z arr  where
    go i s z arr = case i <# s of
        1# -> case indexUnlifted# arr i of
                a -> case from# a of
                  !a -> let !b = f z a in go (i +# 1#) s b arr
        _  -> z
{-# inline foldl' #-}

fromList :: forall a. Unlifted a => [a] -> Array a
fromList xs = case length xs of
  I# size -> Array (runRW# \s ->
     case newArrayArray# size s of
        (# s, marr #) -> go xs 0# s where
            go (x:xs) i s = case writeUnlifted# marr i (to# x) s of s -> go xs (i +# 1#) s
            go _      _ s = case unsafeFreezeArrayArray# marr s of
                              (# _, arr #) -> arr)
{-# inline fromList #-}
