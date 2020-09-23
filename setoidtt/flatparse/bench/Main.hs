{-# options_ghc -Wno-unused-imports #-}

module Main where

import Gauge
import qualified Data.ByteString.Char8 as B

import qualified FP
import qualified FPI
import qualified FPEF
import qualified FPIO
import qualified Attoparsec
import qualified Megaparsec
import qualified Parsec

sexpInp :: B.ByteString
sexpInp =
  B.concat $ "(" : replicate 33333 "(foo (foo (foo ((bar baza)))))" ++ [")"]

longwsInp :: B.ByteString
longwsInp = B.concat $ replicate 55555 "thisisalongkeyword   "

numcsvInp :: B.ByteString
numcsvInp = B.concat ("0" : [B.pack (",  " ++ show n) | n <- [1..100000::Int]])

main :: IO ()
main = defaultMain [
  bgroup "sexp" [
    bench "flatparse"   $ whnf FP.runSexp       sexpInp,
    bench "flatparseIO" $ whnf FPIO.runSexp     sexpInp,
    bench "flatparseef" $ whnf FPEF.runSexp     sexpInp,
    bench "flatparsei"  $ whnf FPI.runSexp        sexpInp,
    bench "attoparsec"  $ whnf Attoparsec.runSexp sexpInp,
    bench "megaparsec"  $ whnf Megaparsec.runSexp sexpInp,
    bench "parsec"      $ whnf Parsec.runSexp     sexpInp
  ],

  bgroup "long keyword" [
    bench "flatparse"   $ whnf FP.runLongws        longwsInp,
    bench "flatparseio" $ whnf FPIO.runLongws      longwsInp,
    bench "flatparseef" $ whnf FPEF.runLongws      longwsInp,
    bench "flatparsei" $ whnf FPI.runLongws        longwsInp,
    bench "attoparsec" $ whnf Attoparsec.runLongws longwsInp,
    bench "megaparsec" $ whnf Megaparsec.runLongws longwsInp,
    bench "parsec"     $ whnf Parsec.runLongws     longwsInp
  ],

  bgroup "numeral csv" [
    bench "flatparse"   $ whnf FP.runNumcsv        numcsvInp,
    bench "flatparseio" $ whnf FPIO.runNumcsv      numcsvInp,
    bench "flatparseef" $ whnf FPEF.runNumcsv      numcsvInp,
    bench "flatparsei" $ whnf FPI.runNumcsv        numcsvInp,
    bench "attoparsec" $ whnf Attoparsec.runNumcsv numcsvInp,
    bench "megaparsec" $ whnf Megaparsec.runNumcsv numcsvInp,
    bench "parsec"     $ whnf Parsec.runNumcsv     numcsvInp
  ]
 ]
