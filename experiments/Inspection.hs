
{-# language TemplateHaskell, MagicHash #-}

module Main where

import Test.Inspection
import Data.Maybe
import GHC.Exts
import System.IO.Unsafe
import Inspection2 (foo)

lhs, rhs :: (a -> b) -> Maybe a -> Bool
lhs f x = isNothing (fmap f x)
rhs f Nothing = True
rhs f (Just _) = False

fac :: Int -> Int
fac 0 = 1
fac n = n * foo n (fac (n - 1))

testFac :: Int# -> Int#
testFac n = case fac (I# n) of I# n -> n

test1 = $(inspectTest $ doesNotUse 'testFac 'I#)

-- inspect $ coreOf 'testFac

main :: IO ()
main = case test1 of
  Failure msg -> putStrLn msg
  Success msg -> putStrLn msg
