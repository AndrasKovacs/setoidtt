{-# language MagicHash, BangPatterns, UnboxedTuples, Strict, TemplateHaskell #-}

module Notes where

import GHC.Prim
import GHC.Types


f :: Int -> Int
f n = n + 2000
{-# noinline f #-}

g :: Int -> [Int]
g 0 = []
g n = ((:) $! f (f (f n))) $! g (n - 1)
-- fact :: Int -> Bool -> Int
-- fact 0 b = if b then 1 else 2
-- fact n b = n * fact (n - 1) b

-- test1 :: (Int -> Int) -> Int -> Int
-- test1 f n = f (n + 100 + 100)

-- test2 :: Int -> Int
-- test2 n = test1 (flip fact False) (n + 1)

-- test3 :: (Int -> Int -> Int) -> (Int -> Int) -> Int -> Int
-- test3 g f n = test2 n

-- data Pair a b = Pair a b
-- test4 f x = Pair (f x) (f x)
