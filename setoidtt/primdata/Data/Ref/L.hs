
module Data.Ref.L where

import GHC.Prim
import GHC.Types
import Data.Unlifted

import IO
import Data.Array.UndefElem

type role Ref representational
data Ref a = Ref (MutVar# RealWorld a)

instance Unlifted (Ref a) where
  type Rep (Ref a) = MutVar# RealWorld a
  to# (Ref r) = r
  {-# inline to# #-}
  from# r = Ref r
  {-# inline from# #-}
  defaultElem = runIO (new undefElem)
  {-# noinline defaultElem #-}

new :: a -> IO (Ref a)
new a = IO (\s -> case newMutVar# a s of
  (# s , r #) -> (# s, Ref r #))
{-# inline new #-}

write :: Ref a -> a -> IO ()
write (Ref r) a = IO (\s -> case writeMutVar# r a s of s -> (# s, () #))
{-# inline write #-}

read :: Ref a -> IO a
read (Ref r) = IO (readMutVar# r)
{-# inline read #-}

modify :: Ref a -> (a -> a) -> IO ()
modify (Ref r) f = IO (\s -> case readMutVar# r s of
  (# s, a #) -> case writeMutVar# r (f a) s of
    s -> (# s, () #))
{-# inline modify #-}

modify' :: Ref a -> (a -> a) -> IO ()
modify' (Ref r) f = IO (\s -> case readMutVar# r s of
  (# s, a #) -> let !a' = f a in case writeMutVar# r a' s of
    s -> (# s, () #))
{-# inline modify' #-}
