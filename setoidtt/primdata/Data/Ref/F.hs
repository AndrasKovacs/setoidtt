
module Data.Ref.F where

import GHC.Prim
import GHC.Types
import GHC.Magic

import Data.Unlifted
import Data.Flat (Flat)
import qualified Data.Flat as F

type role Ref representational
data Ref a = Ref (MutableByteArray# RealWorld)

instance Flat a => Unlifted (Ref a) where
  type Rep (Ref a) = MutableByteArray# RealWorld
  to# (Ref r) = r
  {-# inline to# #-}
  from# r = Ref r
  {-# inline from# #-}
  defaultElem = defaultRef
  {-# inline defaultElem #-}

defaultRef :: forall a. Flat a => Ref a
defaultRef =
  Ref (runRW# (\s -> case newByteArray# (F.size# @a proxy#) s of
    (# s, arr #) -> arr))
{-# specialize noinline defaultRef :: Ref Int #-}
{-# specialize noinline defaultRef :: Ref Char #-}
{-# specialize noinline defaultRef :: Ref Double #-}

new :: forall a. Flat a => a -> IO (Ref a)
new a = IO \s -> case newByteArray# (F.size# @a proxy#) s of
  (# s, arr #) -> case F.writeByteArray# @a arr 0# a s of
    s -> (# s, Ref arr #)
{-# inline new #-}

write :: forall a. Flat a => Ref a -> a -> IO ()
write (Ref r) a = IO (\s -> case F.writeByteArray# @a r 0# a s of
  s -> (# s , () #))
{-# inline write #-}

read :: forall a. Flat a => Ref a -> IO a
read (Ref r) = IO (F.readByteArray# @a r 0#)
{-# inline read #-}

modify :: forall a. Flat a => Ref a -> (a -> a) -> IO ()
modify (Ref r) f = IO (\s -> case F.readByteArray# @a r 0# s of
  (# s, a #) -> case F.writeByteArray# @a r 0# (f a) s of
    s -> (# s, () #))
{-# inline modify #-}
