
module Common (
    module Common
  , FlatParse.Span(..)
  ) where

import qualified Data.ByteString as B
import qualified Language.Haskell.TH as TH

import Data.Bits
import Data.Hashable
import Data.Kind
import Data.String
import FNV164
import FlatParse
-- import GHC.Stack
import Test.Inspection

--------------------------------------------------------------------------------

type Dbg = () :: Constraint
-- type Dbg = HasCallStack

impossible :: Dbg => a
impossible = error "impossible"
{-# noinline impossible #-}

-- strictness/laziness
--------------------------------------------------------------------------------

data Pair a b = a :*: b

infixl 9 $$!
($$!) :: (a -> b) -> a -> b
($$!) f a = f $! a
{-# inline ($$!) #-}

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

newtype MetaVar = MetaVar Int
  deriving (Eq, Ord, Show, Num) via Int

newtype UMetaVar = UMetaVar Int
  deriving (Eq, Ord, Show, Num) via Int

lvlToIx :: Lvl -> Lvl -> Ix
lvlToIx (Lvl envl) (Lvl l) = Ix (envl - l - 1)
{-# inline lvlToIx #-}

--------------------------------------------------------------------------------

newtype RawName = RawName {unRawName :: B.ByteString}
  deriving (Show, IsString, Eq) via B.ByteString

instance Hashable RawName where
  hashWithSalt salt (RawName str) = fnv164 str salt
  {-# inline hashWithSalt #-}

--------------------------------------------------------------------------------

type Name = S WName
data WName
  = WNP
  | WNEmpty
  | WNX
  | WNName RawName
  deriving (Eq, Show)
pattern NP      = S WNP
pattern NEmpty  = S WNEmpty
pattern NX      = S WNX
pattern NName x = S (WNName x)

-- | Pick the more informative name.
pick :: Name -> Name -> Name
pick x y = case x of
  NEmpty -> case y of
    NEmpty -> NX
    y -> y
  x -> x
{-# inline pick #-}

-- Inspection testing
--------------------------------------------------------------------------------

-- | Check that a definition contains no `S` and `unS`. Note: we enable
--   -fplugin-opt=Test.Inspection.Plugin:skip-O0 to stop interactive loading
--   to be killed by inspection failure.
inspectS :: TH.Name -> TH.Q [TH.Dec]
inspectS name = inspect $ mkObligation name (NoUseOf ['S, 'unS])


--------------------------------------------------------------------------------

pickTest x y = unS (pick (S x) (S y))
inspect $ mkObligation 'pickTest (NoUseOf ['S, 'unS])
