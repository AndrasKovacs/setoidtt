
module Common (
    module Common
  , FlatParse.Span(..)
  ) where

import qualified Data.ByteString as B
import Data.String
import GHC.Stack

import FlatParse

--------------------------------------------------------------------------------

impossible :: HasCallStack => a
impossible = error "impossible"
{-# inline impossible #-}

data Icit
  = Impl
  | Expl
  deriving (Eq, Show)

data ArgInfo
  = NoName Icit
  | Named {-# unpack #-} Span
  deriving Show

newtype Ix = Ix Int
  deriving (Eq, Ord, Show, Num) via Int

newtype Lvl = Lvl Int
  deriving (Eq, Ord, Show, Num) via Int

newtype Name = Name B.ByteString
  deriving (Eq, Ord, Show, IsString) via B.ByteString

pick :: Name -> Name -> Name
pick "_" "_" = "x"
pick "_" x   = x
pick x   "_" = x
pick x   y   = x

newtype Meta = Meta Int
  deriving (Eq, Ord, Show, Num) via Int

newtype UMeta = UMeta Int
  deriving (Eq, Ord, Show, Num) via Int
