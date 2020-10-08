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

type S# a = (# a #)
pattern S# :: a -> S# a
pattern S# a = (# a #)
{-# complete S# #-}

data S a = S !a
unS :: S a -> a
unS (S a) = a
{-# inline unS #-}

sFun1 :: (a -> b) -> S a -> S b
sFun1 f (S a) = S (f a)
{-# inline sFun1 #-}

unSFun1 :: (S a -> S b) -> a -> b
unSFun1 f a = unS (f (S a))
{-# inline unSFun1 #-}

instance Show a => Show (S a) where
  showsPrec n (S a) = showsPrec n a

instance Eq a => Eq (S a) where
  S x == S y = x == y
  {-# inline (==) #-}

data L a = L ~a
unL :: L a -> a
unL (L a) = a
{-# inline unL #-}

--------------------------------------------------------------------------------

newtype Unfolding = Unfolding# Int deriving Eq
pattern DoUnfold   = Unfolding# 0
pattern DontUnfold = Unfolding# 1
{-# complete DoUnfold, DontUnfold #-}

instance Show Unfolding where
  show DoUnfold   = "DoUnfold"
  show DontUnfold = "DontUnfold"

newtype Icit = Icit# Int deriving Eq
pattern Impl = Icit# 0
pattern Expl = Icit# 1
{-# complete Impl, Expl #-}

instance Show Icit where
  show Impl = "Impl"
  show Expl = "Expl"

data ArgInfo
  = NoName Icit
  | Named {-# unpack #-} Span
  deriving Show

newtype Ix = Ix Int
  deriving (Eq, Ord, Show, Num) via Int

newtype Lvl = Lvl Int
  deriving (Eq, Ord, Show, Num, Bits) via Int

lvlToIx :: Lvl -> Lvl -> Ix
lvlToIx (Lvl envl) (Lvl l) = Ix (envl - l - 1)
{-# inline lvlToIx #-}

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
