
module Data.Array.SI where

import GHC.Prim
import GHC.Types
import GHC.Magic
import Data.Foldable

import Data.Unlifted
import Data.Array.UndefElem

type role Array representational
data Array a = Array (SmallArray# a)

instance Functor Array where
  fmap = Data.Array.SI.map
  {-# inline fmap #-}

instance Foldable Array where
  foldr  = Data.Array.SI.foldr
  foldr' = foldr'
  foldl' = Data.Array.SI.foldl'
  null arr = size arr == 0
  length = size
  {-# inline foldr  #-}
  {-# inline foldr' #-}
  {-# inline foldl' #-}
  {-# inline null   #-}
  {-# inline length #-}

instance Unlifted (Array a) where
  type Rep (Array a) = SmallArray# a
  to# (Array arr) = arr
  from#           = Array
  {-# inline to# #-}
  {-# inline from# #-}
  defaultElem = empty
  {-# inline defaultElem #-}

instance Show a => Show (Array a) where
  show = show . Data.Array.SI.foldr (:) []
  {-# inline show #-}

new# :: Int# -> a -> SmallArray# a
new# n a = runRW# \s -> case newSmallArray# n a s of
    (# s, marr #) -> case unsafeFreezeSmallArray# marr s of
      (# _, arr #) -> arr
{-# inline new# #-}

new :: Int -> a -> Array a
new (I# n) a = Array (new# n a)
{-# inline new #-}

empty :: Array a
empty = new 0 undefElem
{-# noinline empty #-}

infixl 7 !#
(!#) :: SmallArray# a -> Int# -> (# a #)
(!#) = indexSmallArray#
{-# inline (!#) #-}

infixl 7 !##
(!##) :: Array a -> Int -> (# a #)
(!##) (Array arr) (I# i) = arr !# i
{-# inline (!##) #-}

infixl 7 !
(!) :: Array a -> Int -> a
(!) arr i = case arr !## i of (# a #) -> a
{-# inline (!) #-}

size# :: SmallArray# a -> Int#
size# = sizeofSmallArray#
{-# inline size# #-}

size :: Array a -> Int
size (Array arr) = I# (size# arr)
{-# inline size #-}

clone# :: SmallArray# a -> Int# -> Int# -> SmallArray# a
clone# = cloneSmallArray#
{-# inline clone# #-}

-- | Create a new array from a slice of the input array.
--   `Int` arguments are: offset, slice length.
clone :: Array a -> Int -> Int -> Array a
clone (Array arr) (I# i) (I# s) = Array (clone# arr i s)
{-# inline clone #-}

sizedUpdate# :: Int# -> SmallArray# a -> Int# -> a -> SmallArray# a
sizedUpdate# size arr i a = runRW# \s ->
    case thawSmallArray# arr 0# size s of
        (# s, marr #) -> case writeSmallArray# marr i a s of
            s -> case unsafeFreezeSmallArray# marr s of
              (# s , arr #) -> arr
{-# inline sizedUpdate# #-}

-- | Create a new array where the element at an index is replaced by a given value.
--   The first parameter is the size of the array. If the size is statically known,
--   GHC is often able to generate more efficient copying code.
sizedUpdate :: Int -> Array a -> Int -> a -> Array a
sizedUpdate (I# size) (Array arr) (I# i) a = Array (sizedUpdate# size arr i a)
{-# inline sizedUpdate #-}

-- | Create a new array where the element at an index is replaced by a given value.
--   The first parameter is the size of the array.
update :: Array a -> Int -> a -> Array a
update arr i a = sizedUpdate (size arr) arr i a
{-# inline update #-}

sizedModify# :: Int# -> SmallArray# a -> Int# -> (a -> a) -> SmallArray# a
sizedModify# size arr i f =
  case indexSmallArray# arr i of
    (# a #) -> sizedUpdate# size arr i (f a)
{-# inline sizedModify# #-}

-- | Create a new array where a function is lazily applied to a given element.
--   The first parameter is the size of the array. If the size is
--   statically known, GHC is often able to generate more efficient copying
--   code.
sizedModify :: Int -> Array a -> Int -> (a -> a) -> Array a
sizedModify (I# size) (Array arr) (I# i) f = Array (sizedModify# size arr i f)
{-# inline sizedModify #-}

-- | Create a new array where a function is lazily applied to a given element.
modify :: Array a -> Int -> (a -> a) -> Array a
modify arr i f = sizedModify (size arr) arr i f
{-# inline modify #-}

sizedModify'# :: Int# -> SmallArray# a -> Int# -> (a -> a) -> SmallArray# a
sizedModify'# size arr i f =
  case indexSmallArray# arr i of
    (# a #) -> let !val = f a in sizedUpdate# size arr i val
{-# inline sizedModify'# #-}

-- | Create a new array where a function is strictly applied to a given element.
--   The first parameter is the size of the array. If the size is
--   statically known, GHC is often able to generate more efficient copying
--   code.
sizedModify' :: Int -> Array a -> Int -> (a -> a) -> Array a
sizedModify' (I# size) (Array arr) (I# i) f = Array (sizedModify'# size arr i f)

-- | Create a new array where a function is strictly applied to a given element.
modify' :: Array a -> Int -> (a -> a) -> Array a
modify' arr i f = sizedModify' (size arr) arr i f
{-# inline modify' #-}

sizedMap# :: forall a b. Int# -> (a -> b) ->  SmallArray# a -> SmallArray# b
sizedMap# size f = \arr ->
    let go :: Int# -> SmallMutableArray# s b -> Int# -> State# s -> State# s
        go i marr size s = case i <# size of
            1# -> case indexSmallArray# arr i of
              (# a #) -> case writeSmallArray# marr i (f a) s of
                s -> go (i +# 1#) marr size s
            _  -> s
    in runRW# \s ->
        case newSmallArray# size undefElem s of
            (# s, marr #) -> case go 0# marr size s of
                s -> case unsafeFreezeSmallArray# marr s of
                  (# _ , arr #) -> arr
{-# inline sizedMap# #-}

sizedMap :: forall a b. Int -> (a -> b) -> Array a -> Array b
sizedMap (I# size) f = \(Array arr) -> Array (sizedMap# size f arr)
{-# inline sizedMap #-}

map :: forall a b. (a -> b) -> Array a -> Array b
map f = \arr -> sizedMap (size arr) f arr
{-# inline map #-}

sizedMap'# :: forall a b. Int# -> (a -> b) -> SmallArray# a -> SmallArray# b
sizedMap'# size f = \arr ->
    let go :: Int# -> SmallMutableArray# s b -> Int# -> State# s -> State# s
        go i marr size s = case i <# size of
            1# -> case indexSmallArray# arr i of
              (# a #) -> let !b = f a in case writeSmallArray# marr i b s of
                s -> go (i +# 1#) marr size s
            _  -> s
    in runRW# \s ->
        case newSmallArray# size undefElem s of
            (# s, marr #) -> case go 0# marr size s of
                s -> case unsafeFreezeSmallArray# marr s of
                  (# _ , arr #) -> arr
{-# inline sizedMap'# #-}

sizedMap' :: forall a b. Int -> (a -> b) -> Array a -> Array b
sizedMap' (I# size) f = \(Array arr) -> Array (sizedMap'# size f arr)
{-# inline sizedMap' #-}

map' :: forall a b. (a -> b) -> Array a -> Array b
map' f = \arr -> sizedMap' (size arr) f arr
{-# inline map' #-}

foldr :: forall a b. (a -> b -> b) -> b -> Array a -> b
foldr f z = \(Array arr) -> go 0# (sizeofSmallArray# arr) z arr where
    go :: Int# -> Int# -> b -> SmallArray# a -> b
    go i s z arr = case i <# s of
        1# -> case arr !# i of (# a #) -> f a (go (i +# 1#) s z arr)
        _  -> z
{-# inline foldr #-}

rfoldr :: (a -> b -> b) -> b -> Array a -> b
rfoldr f z = \(Array arr) -> go (sizeofSmallArray# arr -# 1#) z arr where
    go i z arr = case i >=# 0# of
        1# -> case arr !# i of (# a #) -> f a (go (i -# 1#) z arr)
        _  -> z
{-# inline rfoldr #-}

foldl' :: (b -> a -> b) -> b -> Array a -> b
foldl' f z = \(Array arr) -> go 0# (sizeofSmallArray# arr) z arr  where
    go i s z arr = case i <# s of
        1# -> case arr !# i of
                (# a #) -> let !b = f z a in go (i +# 1#) s b arr
        _  -> z
{-# inline foldl' #-}

rfoldl' :: (b -> a -> b) -> b -> Array a -> b
rfoldl' f z = \(Array arr) -> go (sizeofSmallArray# arr -# 1#) z arr where
    go i z arr = case i >=# 0# of
        1# -> case arr!# i of
                (# a #) -> let !b = f z a in go (i -# 1#) b arr
        _  -> z
{-# inline rfoldl' #-}

fromList :: [a] -> Array a
fromList xs = case length xs of
  I# size -> Array (runRW# \s ->
     case newSmallArray# size undefElem s of
        (# s, marr #) -> go xs 0# s where
            go (x:xs) i s = case writeSmallArray# marr i x s of s -> go xs (i +# 1#) s
            go _      _ s = case unsafeFreezeSmallArray# marr s of
                              (# _, arr #) -> arr)
{-# inline fromList #-}
