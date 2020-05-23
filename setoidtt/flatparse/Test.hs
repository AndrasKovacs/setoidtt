{-# language TupleSections #-}
{-# options_ghc -Wno-unused-imports #-}

module Test where

import qualified Data.ByteString.Char8 as B
import FlatParseIndent
import Data.Bits
import Data.Word
import Data.List
import Language.Haskell.TH hiding (match)
import Data.Char

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import GHC.Exts


foo = $(string "foobar")

-- test1 = ($(char '(') *> test1 <* $(char ')')) <|> pure ()

-- test2 =
--   br $(char '(') (test2 <* $(char ')')) $
--   pure ()



-- -- test =
-- --   $(wordSet ["while", "if", "then", "else", "let", "in", "do", "letrec"])

-- bar = $(string "bar")

-- -- kek = $(match [
-- --   ("kek" , [| bar |]),
-- --   ("lole", [| $(string "foo") >> bar >> bar |])
-- --   ])

-- kek = $(match[| case _ of
--   "foo" -> _
--   "bar" -> _
--   "baz" -> _
--   |])
