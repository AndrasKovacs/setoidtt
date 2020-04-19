
module Data.Array.LIU where

import GHC.Types
import GHC.Magic
import GHC.Prim

import Data.Unlifted
import Data.Array.UndefElem
import qualified Data.Array.LIL as A


type role Array representational
newtype Array a = Array (A.Array Any)
  deriving Unlifted

instance (Unlifted a, Show a) => Show (Array a) where
  show = show . toList
  {-# inline show #-}

new :: Unlifted a => Int -> a -> Array a
new i a = case toUnlifted# a of a -> Array (A.new i (unsafeCoerce# a))
{-# inline new #-}

empty :: Array a
empty = Array A.empty
{-# noinline empty #-}

infixl 4 !
(!) :: Unlifted a => Array a -> Int -> a
(!) (Array arr) i = case arr A.!## i of
  (# a #) -> case fromUnlifted# (unsafeCoerce# a) of
    !a -> a
{-# inline (!) #-}

size :: Array a -> Int
size (Array arr) = A.size arr
{-# inline size #-}

-- | Create a new array from a slice of the input array.
--   `Int` arguments are: offset, slice length.
clone :: Array a -> Int -> Int -> Array a
clone (Array arr) i s = Array (A.clone arr i s)
{-# inline clone #-}

-- | Create a new array where the element at an index is replaced by a given value.
--   The first parameter is the size of the array. If the size is statically known,
--   GHC is often able to generate more efficient copying code.
sizedUpdate :: Unlifted a => Int -> Array a -> Int -> a -> Array a
sizedUpdate size (Array arr) i a =
  case toUnlifted# a of
    a -> Array (A.sizedUpdate size arr i (unsafeCoerce# a))
{-# inline sizedUpdate #-}

-- | Create a new array where the element at an index is replaced by a given value.
--   The first parameter is the size of the array.
update :: Unlifted a => Array a -> Int -> a -> Array a
update (Array arr) i a =
  case toUnlifted# a of
    a -> Array (A.update arr i (unsafeCoerce# a))
{-# inline update #-}

-- | Create a new array where a function is lazily applied to a given element.
--   The first parameter is the size of the array. If the size is
--   statically known, GHC is often able to generate more efficient copying
--   code.
sizedModify :: forall a. Unlifted a => Int -> Array a -> Int -> (a -> a) -> Array a
sizedModify size arr i f = case toUnlifted# (f (arr ! i)) of
  a -> sizedUpdate size arr i (unsafeCoerce# a)
{-# inline sizedModify #-}

-- | Create a new array where a function is lazily applied to a given element.
modify :: Unlifted a => Array a -> Int -> (a -> a) -> Array a
modify arr i f = sizedModify (size arr) arr i f
{-# inline modify #-}

sizedMap :: forall a b. (Unlifted a, Unlifted b) => Int
             -> (a -> b) -> Array a -> Array b
sizedMap (I# size) f = \(Array (A.Array arr)) ->
    let go :: Int# -> MutableArray# s Any -> Int# -> State# s -> State# s
        go i marr size s = case i <# size of
            1# -> case arr A.!# i of
              (# a #) -> case f $! fromUnlifted# (unsafeCoerce# a) of
                !a -> case toUnlifted# a of
                  a -> case writeArray# marr i (unsafeCoerce# a) s of
                    s -> go (i +# 1#) marr size s
            _  -> s
    in runRW# $ \s ->
        case newArray# size undefElem s of
            (# s, marr #) -> case go 0# marr size s of
                s -> case unsafeFreezeArray# marr s of
                  (# _ , arr #) -> Array (A.Array arr)
{-# inline sizedMap #-}

map :: forall a b. (Unlifted a, Unlifted b) => (a -> b) -> Array a -> Array b
map f = \arr -> sizedMap (size arr) f arr
{-# inline map #-}

foldr :: forall a b. Unlifted a => (a -> b -> b) -> b -> Array a -> b
foldr f z = \(Array arr) ->
  A.foldr (\a b -> (f $! (fromUnlifted# (unsafeCoerce# a))) b) z arr
{-# inline foldr #-}

rfoldr :: Unlifted a => (a -> b -> b) -> b -> Array a -> b
rfoldr f z = \(Array arr) -> A.rfoldr (\a b -> (f $! (fromUnlifted# (unsafeCoerce# a))) b) z arr
{-# inline rfoldr #-}

foldl' :: Unlifted a => (b -> a -> b) -> b -> Array a -> b
foldl' f z = \(Array arr) -> A.foldl' (\b a -> f b $! (fromUnlifted# (unsafeCoerce# a))) z arr
{-# inline foldl' #-}

rfoldl' :: Unlifted a => (b -> a -> b) -> b -> Array a -> b
rfoldl' f z = \(Array arr) -> A.rfoldl' (\b a -> f b $! (fromUnlifted# (unsafeCoerce# a))) z arr
{-# inline rfoldl' #-}

fromList :: Unlifted a => [a] -> Array a
fromList = \xs -> runRW# $ \s ->
  case length xs of
      I# size -> case newArray# size undefElem s of
        (# s, marr #) -> go xs 0# s where
            go (x:xs) i s = case toUnlifted# x of
                             x -> case writeArray# marr i (unsafeCoerce# x) s of
                               s -> go xs (i +# 1#) s
            go _      _ s = case unsafeFreezeArray# marr s of
                              (# _, arr #) -> Array (A.Array arr)
{-# inline fromList #-}

toList :: Unlifted a => Array a -> [a]
toList = Data.Array.LIU.foldr (:) []
{-# inline toList #-}
