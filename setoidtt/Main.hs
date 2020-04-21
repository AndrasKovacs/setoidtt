

module Main where

-- import qualified Data.Array.FI as FI
import qualified Data.Array.Dynamic.L as DL

main :: IO ()
main = do
  !arr <- DL.empty @Int
  DL.push arr 0
