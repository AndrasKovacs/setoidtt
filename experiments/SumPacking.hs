
{-# language UnboxedTuples, UnboxedSums, MagicHash, Strict, BangPatterns #-}
{-# options_ghc -fno-full-laziness #-}

module Main where

import GHC.Prim
import GHC.Types


i16 :: Int -> Int16#
i16 (I# x) = narrowInt16# x
{-# inline i16 #-}


data Test  = Nil | Cons Int16# Int16# Int16# Int16# Test
data Test2 = Nil2 | Cons2 (# (# Int16#, Int16#, Int16#, Int16# #) | Int16# #) Test

main :: IO ()
main = do
  print (I# (closureSize# (Cons (i16 0) (i16 0) (i16 0) (i16 0) Nil)))
  print (I# (closureSize# (Cons2 (# (# (i16 0), (i16 0), (i16 0), (i16 0) #) | #)Nil)))
