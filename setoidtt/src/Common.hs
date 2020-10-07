{-# options_ghc -Wno-unused-imports #-}

module Common (
    module Common
  , FlatParse.Span(..)
  ) where

import qualified Data.ByteString as B
import Data.Kind
import GHC.Stack
import Data.Bits
import FlatParse

--------------------------------------------------------------------------------

type Dbg = () :: Constraint
-- type Dbg = HasCallStack

impossible :: Dbg => a
impossible = error "impossible"
{-# noinline impossible #-}

infixl 9 $$!
($$!) :: (a -> b) -> a -> b
($$!) f a = f $! a
{-# inline ($$!) #-}

data S a = S !a

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
  deriving (Eq, Ord, Show, Num, Bits) via Int

data Name = NP | NNil | NX | NName B.ByteString
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
