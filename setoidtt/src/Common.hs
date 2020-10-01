
module Common (
    module Common
  , FlatParse.Span(..)
  ) where

import qualified Data.ByteString as B
import qualified Data.IntSet as IS
import Data.String

import FlatParse

--------------------------------------------------------------------------------

data Icit
  = Impl
  | Expl
  deriving Show

data ArgInfo
  = NoName Icit
  | Named Span
  deriving Show

newtype Ix = Ix Int
  deriving (Eq, Ord, Show, Num) via Int

newtype Lvl = Lvl Int
  deriving (Eq, Ord, Show, Num) via Int

newtype Name = Name B.ByteString
  deriving (Eq, Ord, Show, IsString) via B.ByteString

newtype Meta = Meta Int
  deriving (Eq, Ord, Show, Num) via Int

data U
  = Set
  | UMax IS.IntSet   -- ^ Maximum of a set of universe metas. Empty set = Prop.
  deriving Show
