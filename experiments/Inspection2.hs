
module Inspection2 where

foo :: Int -> Int -> Int
foo n m | even n    = 0
        | otherwise = m
