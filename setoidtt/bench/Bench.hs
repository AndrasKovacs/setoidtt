
module Main where

import Parser
import Paths_setoidtt
import Presyntax

topLength :: TopLevel -> Int
topLength = go 0 where
  go acc Nil = acc
  go acc (Define _ _ _ t) = go (acc + 1) t
  go acc (Postulate _ _ t) = go (acc + 1) t

main :: IO ()
main = do
  path <- getDataFileName "bench/parse01.stt"
  res <- parseFile path
  print $ topLength res
