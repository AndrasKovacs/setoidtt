
module Main where

import Gauge
import qualified Data.ByteString as B

import qualified ParsersSexp
import qualified AttoSexp
import qualified MegaSexp

sexpInp :: B.ByteString
sexpInp =
  B.concat $ "(" : replicate 333333 "(foo (foo (foo ((bar baza)))))" ++ [")"]

main :: IO ()
main = defaultMain [
  bench "parsers-sexp"    $ whnf ParsersSexp.run sexpInp,
  bench "attoparsec-sexp" $ whnf AttoSexp.run    sexpInp,
  bench "megaparsec-sexp" $ whnf MegaSexp.run    sexpInp
  ]
