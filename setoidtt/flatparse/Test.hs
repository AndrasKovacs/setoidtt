{-# language TupleSections #-}
{-# options_ghc -Wno-unused-imports #-}

module Test where

import qualified Data.ByteString.Char8 as B
import FlatParse
import Data.Bits
import Data.Word
import Data.List
import Language.Haskell.TH
import Data.Char

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import GHC.Exts

test =
  $(wordSet ["while", "if", "then", "else", "let", "in", "do", "letrec"])
