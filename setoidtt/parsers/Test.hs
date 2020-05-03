{-# options_ghc -Wno-unused-imports #-}

module Test where

import FlatParse
import Data.Bits
import Data.Word
import Data.List
import Language.Haskell.TH

import qualified Data.ByteString.Char8 as B

-- inp = B.replicate 8192 'a' <> "bb"
-- ws = many_ ($(someChar ' ') <|> $(someChar '\n'))
