
module Common (
    module Common
  , FlatParse.Span(..)
  ) where

import qualified Data.ByteString as B
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

data Name = NP | NNil | NX | NName {-# unpack #-} B.ByteString
  deriving (Eq, Show)

-- | Pick the more informative name.
pick :: Name -> Name -> Name
pick x y = case x of
  NNil -> case y of
    NNil -> NX
    y -> y
  x -> x
{-# inline pick #-}

newtype Meta = Meta Int
  deriving (Eq, Ord, Show, Num) via Int

newtype UMeta = UMeta Int
  deriving (Eq, Ord, Show, Num) via Int
