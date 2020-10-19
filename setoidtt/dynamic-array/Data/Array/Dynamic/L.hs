
module Data.Array.Dynamic.L  (
    empty
  , Array
  , clear
  , push
  , Data.Array.Dynamic.L.read
  , Data.Array.Dynamic.L.show
  , size
  , unsafeRead
  , unsafeWrite
  , write
  , modify'
  , unsafeLast
  , Data.Array.Dynamic.L.last
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
import qualified Data.Array.LM as LM

type role Array representational
newtype Array (a :: *) = Array (RUU.Ref (RF.Ref Int) (LM.Array a))
  deriving Unlifted

defaultCapacity :: Int
defaultCapacity = 5
{-# inline defaultCapacity #-}

empty :: forall a. IO (Array a)
empty = do
  sizeRef <- RF.new 0
  arrRef  <- LM.new defaultCapacity undefElem
  Array <$> RUU.new sizeRef arrRef
{-# inline empty #-}

unsafeRead :: Array a -> Int -> IO a
unsafeRead (Array r) i = do
  elems <- RUU.readSnd r
  LM.read elems i
{-# inline unsafeRead #-}

read :: Array a -> Int -> IO a
read (Array r) i = do
  elems <- RUU.readSnd r
  if 0 <= i && i < LM.size elems then
    LM.read elems i
  else
    error "Data.Array.Dynamic.L.read: out of bounds"
{-# inline read #-}

unsafeWrite :: Array a -> Int -> a -> IO ()
unsafeWrite (Array r) i a = do
  elems <- RUU.readSnd r
  LM.write elems i a
{-# inline unsafeWrite #-}

write :: Array a -> Int -> a -> IO ()
write (Array r) i ~a = do
  s <- RF.read =<< RUU.readFst r
  if 0 <= i && i < s then
    unsafeWrite (Array r) i a
  else
    error "Data.Array.Dynamic.L.write: out of bounds"
{-# inline write #-}

modify' :: Array a -> Int -> (a -> a) -> IO ()
modify' (Array r) i f = do
  s <- RF.read =<< RUU.readFst r
  if 0 <= i && i < s then do
    elems <- RUU.readSnd r
    LM.modify' elems i f
  else
    error "Data.Array.Dynamic.L.write: out of bounds"
{-# inline modify' #-}

extendCapacity :: RUU.Ref (RF.Ref Int) (LM.Array a) -> a -> Int -> LM.Array a -> IO ()
extendCapacity r ~a cap elems = do
  let cap' = 2 * cap
  elems' <- LM.new cap' undefElem
  LM.copySlice elems 0 elems' 0 cap
  LM.write elems' cap a
  RUU.writeSnd r elems'
{-# inlinable extendCapacity #-}

push :: Array a -> a -> IO ()
push (Array r) ~a = do
  sizeRef <- RUU.readFst r
  elems   <- RUU.readSnd r
  size    <- RF.read sizeRef
  let cap = LM.size elems
  RF.write sizeRef (size + 1)
  if (size == cap) then do
    extendCapacity r a cap elems
  else do
    LM.write elems size a
{-# inline push #-}

clear :: Array a -> IO ()
clear (Array r) = do
  (`RF.write` 0) =<< RUU.readFst r
  RUU.writeSnd r =<< LM.new defaultCapacity undefElem
{-# inline clear #-}

size :: Array a -> IO Int
size (Array r) = RF.read =<< RUU.readFst r
{-# inline size #-}

unsafeLast :: Array a -> IO a
unsafeLast arr = do
  i <- size arr
  Data.Array.Dynamic.L.unsafeRead arr (i - 1)
{-# inline unsafeLast #-}

isEmpty :: Array a -> IO Bool
isEmpty arr = (==0) <$> size arr
{-# inline isEmpty #-}

last :: Array a -> IO a
last arr = do
  i <- size arr
  isEmpty arr >>= \case
    True -> error "Data.Array.Dynamic.last: empty array"
    _    -> unsafeRead arr (i - 1)
{-# inline last #-}

show :: Show a => Array a -> IO String
show (Array r) = do
  elems  <- RUU.readSnd r
  size <- RF.read =<< RUU.readFst r
  elems' <- LM.freezeSlice elems 0 size
  pure (Prelude.show elems')

-- foldl' :: forall a b. (b -> a -> b) -> b -> Array a -> IO b
-- foldl' f b = \arr -> _

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
