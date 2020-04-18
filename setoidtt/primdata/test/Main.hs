
{-# options_ghc -Wno-unused-imports #-}

module Main where

import GHC.Prim
import GHC.Types
import GHC.Magic

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.QuickCheck

import qualified Data.Array.LIL as LIL
import qualified Data.Array.LIU as LIU

import Data.Unlifted

import Debug.Trace
-- import qualified Data.Array.LML as LML
-- import qualified Data.Array.LMU as LMU
-- import qualified Data.Array.SIL as SIL
-- import qualified Data.Array.SIU as SIU
-- import qualified Data.Array.SML as SML
-- import qualified Data.Array.SMU as SMU

main :: IO ()
main = do
  let a = LIL.fromList [0..10::Int]
  let foo = LIU.fromList [a]
  print (foo LIU.! 0)
