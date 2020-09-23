{-# options_ghc -Wno-unused-imports #-}

module StringTrie.Trie where

import Data.Char
import Data.Bits
import Data.Word

newtype Prefix = Prefix Int


instance Show Prefix where
  show = undefined

data Node a = Node {
  _prefix :: Prefix,
  _value  :: a,
  _child  :: Trie a,
  _next   :: Trie a
  }
  deriving Show

data Trie a
  = Zero
  | One {-# unpack #-} (Node a)
  | Two {-# unpack #-} (Node a) {-# unpack #-} (Node a)
  deriving Show
