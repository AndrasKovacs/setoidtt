
module Data.Array.Dynamic.U  (
    empty
  , Array
  , clear
  , push
  , Data.Array.Dynamic.U.read
  , Data.Array.Dynamic.U.show
  , size
  , unsafeRead
  , unsafeWrite
  , write
  , unsafeLast
  , Data.Array.Dynamic.U.last
  , isEmpty
  -- , foldl'
  -- , foldlIx'
  -- , foldr'
  -- , foldrIx'
  -- , Data.Array.Dynamic.any
  -- , Data.Array.Dynamic.all
  -- , allIx
  -- , anyIx
  -- , forM_
  -- , forMIx_
  ) where

import Data.Unlifted
import Data.Array.UndefElem

import qualified Data.Ref.UU   as RUU
import qualified Data.Ref.F    as RF
import qualified Data.Array.UM as UM

type role Array representational
newtype Array (a :: *) = Array (RUU.Ref (RF.Ref Int) (UM.Array a))
  deriving Unlifted

defaultCapacity :: Int
defaultCapacity = 5
{-# inline defaultCapacity #-}

empty :: forall a. Unlifted a => IO (Array a)
empty = do
  sizeRef <- RF.new 0
  arrRef  <- UM.new defaultCapacity defaultElem
  Array <$> RUU.new sizeRef arrRef
{-# inline empty #-}

unsafeRead :: Unlifted a => Array a -> Int -> IO a
unsafeRead (Array r) i = do
  elems <- RUU.readSnd r
  UM.read elems i
{-# inline unsafeRead #-}

read :: Unlifted a => Array a -> Int -> IO a
read (Array r) i = do
  elems <- RUU.readSnd r
  if 0 <= i && i < UM.size elems then
    UM.read elems i
  else
    error "Data.Array.Dynamic.U.read: out of bounds"
{-# inline read #-}

unsafeWrite :: Unlifted a => Array a -> Int -> a -> IO ()
unsafeWrite (Array r) i a = do
  elems <- RUU.readSnd r
  UM.write elems i a
{-# inline unsafeWrite #-}

write :: Unlifted a => Array a -> Int -> a -> IO ()
write (Array r) i ~a = do
  s <- RF.read =<< RUU.readFst r
  if 0 <= i && i < s
    then unsafeWrite (Array r) i a
    else error "Data.Array.Dynamic.U.write: out of bounds"
{-# inline write #-}

push :: Unlifted a => Array a -> a -> IO ()
push (Array r) ~a = do
  sizeRef <- RUU.readFst r
  elems   <- RUU.readSnd r
  size    <- RF.read sizeRef
  let cap = UM.size elems
  RF.write sizeRef (size + 1)
  if (size == cap) then do
    let cap' = 2 * cap
    elems' <- UM.new cap' undefElem
    UM.copySlice elems 0 elems' 0 size
    UM.write elems' size a
    RUU.writeSnd r elems'
  else do
    UM.write elems size a
{-# inline push #-}

clear :: Unlifted a => Array a -> IO ()
clear (Array r) = do
  (`RF.write` 0) =<< RUU.readFst r
  RUU.writeSnd r =<< UM.new defaultCapacity undefElem
{-# inline clear #-}

size :: Array a -> IO Int
size (Array r) = RF.read =<< RUU.readFst r
{-# inline size #-}

unsafeLast :: Unlifted a => Array a -> IO a
unsafeLast arr = do
  i <- size arr
  Data.Array.Dynamic.U.unsafeRead arr (i - 1)
{-# inline unsafeLast #-}

isEmpty :: Array a -> IO Bool
isEmpty arr = (==0) <$> size arr
{-# inline isEmpty #-}

last :: Unlifted a => Array a -> IO a
last arr = do
  i <- size arr
  isEmpty arr >>= \case
    True -> error "Data.Array.Dynamic.last: empty array"
    _    -> unsafeRead arr (i - 1)
{-# inline last #-}

show :: (Show a, Unlifted a) => Array a -> IO String
show (Array r) = do
  elems  <- RUU.readSnd r
  size <- RF.read =<< RUU.readFst r
  elems' <- UM.freezeSlice elems 0 size
  pure (Prelude.show elems')
{-# inlinable show #-}

-- foldl' :: (b -> a -> b) -> b -> Array a -> IO b
-- foldl' f b = \arr -> do
--   s <- size arr
--   let go i b | i == s    = pure b
--              | otherwise = do
--                  a <- unsafeRead arr i
--                  go (i + 1) $! f b a
--   go 0 b
-- {-# inline foldl' #-}

-- foldlIx' :: (Int -> b -> a -> b) -> b -> Array a -> IO b
-- foldlIx' f b = \arr -> do
--   s <- size arr
--   let go i b | i == s    = pure b
--              | otherwise = do
--                  a <- unsafeRead arr i
--                  go (i + 1) $! f i b a
--   go 0 b
-- {-# inline foldlIx' #-}

-- foldr' :: (a -> b -> b) -> b -> Array a -> IO b
-- foldr' f b = \arr -> do
--   s <- size arr
--   let go i b | i == (-1) = pure b
--              | otherwise = do
--                  a <- unsafeRead arr i
--                  go (i - 1) $! f a b
--   go (s - 1) b
-- {-# inline foldr' #-}

-- foldrIx' :: (Int -> a -> b -> b) -> b -> Array a -> IO b
-- foldrIx' f b = \arr -> do
--   s <- size arr
--   let go i b | i == (-1) = pure b
--              | otherwise = do
--                  a <- unsafeRead arr i
--                  go (i - 1) $! f i a b
--   go (s - 1) b
-- {-# inline foldrIx' #-}

-- -- TODO: any + all with lazy fold
-- any :: (a -> Bool) -> Array a -> IO Bool
-- any f = foldl' (\b a -> f a || b) False
-- {-# inline any #-}

-- all :: (a -> Bool) -> Array a -> IO Bool
-- all f = foldl' (\b a -> f a && b) True
-- {-# inline all #-}

-- anyIx :: (Int -> a -> Bool) -> Array a -> IO Bool
-- anyIx f = foldlIx' (\i b a -> f i a || b) False
-- {-# inline anyIx #-}

-- allIx :: (Int -> a -> Bool) -> Array a -> IO Bool
-- allIx f = foldlIx' (\i b a -> f i a && b) True
-- {-# inline allIx #-}

-- forM_ :: Array a -> (a -> IO b) -> IO ()
-- forM_ arr f = go (0 :: Int) where
--   go i = do
--     s <- size arr
--     if i == s then pure () else do {x <- unsafeRead arr i; f x; go (i + 1)}
-- {-# inline forM_ #-}

-- forMIx_ :: Array a -> (Int -> a -> IO b) -> IO ()
-- forMIx_ arr f = go (0 :: Int) where
--   go i = do
--     s <- size arr
--     if i == s then pure () else do {x <- unsafeRead arr i; f i x; go (i + 1)}
-- {-# inline forMIx_ #-}
